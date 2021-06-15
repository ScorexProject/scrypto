package scorex.crypto.authds.avltree.batch

import com.google.common.primitives.Ints
import scorex.crypto.authds._
import scorex.crypto.hash.{Blake2b256, CryptographicHash, Digest}
import scorex.util.ScorexLogging
import scorex.utils.ByteArray

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.{Failure, Random, Success, Try}


/**
  * Implements the batch AVL prover from https://eprint.iacr.org/2016/994
  * Not thread safe if you use with ThreadUnsafeHash
  *
  * @param keyLength           - length of keys in tree
  * @param valueLengthOpt      - length of values in tree. None if it is not fixed
  * @param oldRootAndHeight    - option root node and height of old tree. Tree should contain new nodes only
  *                            WARNING if you pass it, all isNew and visited flags should be set correctly and height should be correct
  * @param collectChangedNodes - changed nodes will be collected to a separate buffer during tree modifications if `true`
  * @param hf                  - hash function
  */
class BatchAVLProver[D <: Digest, HF <: CryptographicHash[D]](val keyLength: Int,
                                                              val valueLengthOpt: Option[Int],
                                                              oldRootAndHeight: Option[(ProverNodes[D], Int)] = None,
                                                              val collectChangedNodes: Boolean = true)
                                                             (implicit val hf: HF = Blake2b256)
  extends AuthenticatedTreeOps[D] with ToStringHelper with ScorexLogging {

  protected val labelLength: Int = hf.DigestSize

  private[batch] var topNode: ProverNodes[D] = oldRootAndHeight.map(_._1).getOrElse({
    val t = new ProverLeaf(NegativeInfinityKey,
      ADValue @@ Array.fill(valueLengthOpt.getOrElse(0))(0: Byte), PositiveInfinityKey)
    t.isNew = false
    t
  })

  /**
    * Longest path length in a tree
    */
  var rootNodeHeight: Int = oldRootAndHeight.map(_._2).getOrElse(0)

  private var oldTopNode = topNode

  // Directions are just a bit string representing booleans
  private var directions = new mutable.ArrayBuffer[Byte]
  private var directionsBitLength: Int = 0

  private var replayIndex = 0
  // Keeps track of where we are when replaying directions
  // a second time; needed for deletions
  private var lastRightStep = 0
  // Keeps track of the last time we took a right step
  // when going down the tree; needed for deletions
  private var found: Boolean = false // keeps track of whether the key for the current
  // operation has already been found in the tree
  // (if so, we know how to get to the leaf without
  //  any further comparisons)

  /**
    * Figures out whether to go left or right when from node r when searching for the key;
    * records the appropriate bit in the directions bit string to be used in the proof
    *
    * @param key
    * @param r
    * @return - true if to go left, false if to go right in the search
    */
  protected def nextDirectionIsLeft(key: ADKey, r: InternalNode[D]): Boolean = {
    val ret = if (found) {
      true
    } else {
      ByteArray.compare(key, r.asInstanceOf[InternalProverNode[D]].key) match {
        case 0 => // found in the tree -- go one step right, then left to the leaf
          found = true
          lastRightStep = directionsBitLength
          false
        case o if o < 0 => // going left
          true
        case _ => // going right
          false
      }
    }
    // encode Booleans as bits
    if ((directionsBitLength & 7) == 0) {
      // new byte needed
      directions += (if (ret) 1: Byte else 0: Byte)
    } else {
      if (ret) {
        val i = directionsBitLength >> 3
        directions(i) = (directions(i) | (1 << (directionsBitLength & 7))).toByte // change last byte
      }
    }
    directionsBitLength += 1
    ret
  }

  /**
    * Determines if the leaf r contains the key
    *
    * @param key
    * @param r
    * @return
    */
  protected def keyMatchesLeaf(key: ADKey, r: Leaf[D]): Boolean = {
    // The prover doesn't actually need to look at the leaf key,
    // because the prover would have already seen this key on the way
    // down the to leaf if and only if the leaf matches the key that is being sought
    val ret = found
    found = false // reset for next time
    ret
  }

  /**
    * Deletions go down the tree twice -- once to find the leaf and realize
    * that it needs to be deleted, and the second time to actually perform the deletion.
    * This method will re-create comparison results using directions array and lastRightStep
    * variable. Each time it's called, it will give the next comparison result of
    * key and node.key, where node starts at the root and progresses down the tree
    * according to the comparison results.
    *
    * @return - result of previous comparison of key and relevant node's key
    */
  protected def replayComparison: Int = {
    val ret = if (replayIndex == lastRightStep) {
      0
    } else if ((directions(replayIndex >> 3) & (1 << (replayIndex & 7)).toByte) == 0) {
      1
    } else {
      -1
    }
    replayIndex += 1
    ret
  }

  /**
    * @param r
    * @param key
    * @param v
    * @return - A new prover node with two leaves: r on the left and a new leaf containing key and value on the right
    */
  protected def addNode(r: Leaf[D], key: ADKey, v: ADValue): InternalProverNode[D] = {
    val n = r.nextLeafKey
    new InternalProverNode(key, r.getNew(newNextLeafKey = key).asInstanceOf[ProverLeaf[D]],
      new ProverLeaf(key, v, n), Balance @@ 0.toByte)
  }

  /**
    * Returns the current digest of the authenticated data structure,
    * which contains the root hash and the root height
    *
    * @return - the digest
    */
  def digest: ADDigest = digest(topNode)


  /**
    * If operation.key exists in the tree and the operation succeeds,
    * returns Success(Some(v)), where v is the value associated with operation.key
    * before the operation.
    * If operation.key does not exists in the tree and the operation succeeds, returns Success(None).
    * Returns Failure if the operation fails.
    * Does not modify the tree or the proof in case return is Failure.
    *
    * @param operation
    * @return - Success(Some(old value)), Success(None), or Failure
    */
  def performOneOperation(operation: Operation): Try[Option[ADValue]] = Try {
    replayIndex = directionsBitLength
    returnResultOfOneOperation(operation, topNode) match {
      case Success(n) =>
        topNode = n._1.asInstanceOf[ProverNodes[D]]
        n._2
      case Failure(e) =>
        // take the bit length before fail and divide by 8 with rounding up
        val oldDirectionsByteLength = (replayIndex + 7) / 8
        // undo the changes to the directions array
        directions.trimEnd(directions.length - oldDirectionsByteLength)
        directionsBitLength = replayIndex
        if ((directionsBitLength & 7) > 0) {
          // 0 out the bits of the last element of the directions array
          // that are above directionsBitLength
          val mask = (1 << (directionsBitLength & 7)) - 1
          directions(directions.length - 1) = (directions(directions.length - 1) & mask).toByte
        }
        throw e
    }
  }

  /**
    * @return nodes, that where presented in old tree (starting form oldTopNode, but are not presented in new tree
    */
  def removedNodes(): List[ProverNodes[D]] = {
    changedNodesBufferToCheck.foreach { cn =>
      if (!contains(cn)) changedNodesBuffer += cn
    }
    // .toList is important here, otherwise mutable object will be returned that will be changed during further modifications
    changedNodesBuffer.toList
  }

  /**
    * @return `true` if this tree has an element that has the same label, as `node.label`, `false` otherwise.
    */
  def contains(node: ProverNodes[D]): Boolean = contains(node.key, node.label)

  /**
    * @return `true` if this tree has an element that has the same label, as `node.label`, `false` otherwise.
    */
  def contains(key: ADKey, label: D): Boolean = {
    @tailrec
    def loop(currentNode: ProverNodes[D], keyFound: Boolean): Boolean = {
      currentNode match {
        case _ if currentNode.label sameElements label => true
        case r: InternalProverNode[D] =>
          if (keyFound) {
            loop(r.left, keyFound = true)
          } else {
            ByteArray.compare(key, r.key) match {
              case 0 => // found in the tree -- go one step right, then left to the leaf
                loop(r.right, keyFound = true)
              case o if o < 0 => // going left, not yet found
                loop(r.left, keyFound = false)
              case _ => // going right, not yet found
                loop(r.right, keyFound = false)
            }
          }
        case _ => false
      }
    }

    loop(topNode, keyFound = false)
  }

  /**
    * Generates the proof for all the operations in the list.
    * Does NOT modify the tree
    */
  def generateProofForOperations(operations: Seq[Operation]): Try[(SerializedAdProof, ADDigest)] = Try {
    val newProver = new BatchAVLProver[D, HF](keyLength, valueLengthOpt, Some(topNode, rootNodeHeight), false)
    operations.foreach(o => newProver.performOneOperation(o).get)
    (newProver.generateProof(), newProver.digest)
  }

  /**
    * Generates the proof for all the operations performed (except the ones that failed)
    * since the last generateProof call
    *
    * @return - the proof
    */
  def generateProof(): SerializedAdProof = {
    changedNodesBuffer.clear()
    changedNodesBufferToCheck.clear()
    val packagedTree = new mutable.ArrayBuffer[Byte]
    var previousLeafAvailable = false

    /* TODO Possible optimizations:
     * - Don't put in the key if it's in the modification stream somewhere 
     *   (savings ~32 bytes per proof for transactions with existing key; 0 for insert)
     *   (problem is that then verifier logic has to change -- 
     *   can't verify tree immediately)
     * - Condense a sequence of balances and other non-full-byte info using 
     *   bit-level stuff and maybe even "changing base without losing space" 
     *   by Dodis-Patrascu-Thorup STOC 2010 (expected savings: 5-15 bytes 
     *   per proof for depth 20, based on experiments with gzipping the array
     *   that contains only this info)
     * - Condense the sequence of values if they are mostly not randomly distributed
     * */
    def packTree(rNode: ProverNodes[D]): Unit = {
      // Post order traversal to pack up the tree
      if (!rNode.visited) {
        packagedTree += LabelInPackagedProof
        packagedTree ++= rNode.label
        assert(rNode.label.length == labelLength)
        previousLeafAvailable = false
      } else {
        rNode.visited = false
        rNode match {
          case r: ProverLeaf[D] =>
            packagedTree += LeafInPackagedProof
            if (!previousLeafAvailable) packagedTree ++= r.key
            packagedTree ++= r.nextLeafKey
            if (valueLengthOpt.isEmpty) {
              packagedTree ++= Ints.toByteArray(r.value.length)
            }
            packagedTree ++= r.value
            previousLeafAvailable = true
          case r: InternalProverNode[D] =>
            packTree(r.left)
            packTree(r.right)
            packagedTree += r.balance
        }
      }
    }

    // Recursively reset the new flags
    def resetNew(r: ProverNodes[D]): Unit = {
      r match {
        case rn: InternalProverNode[D] =>
          resetNew(rn.left)
          resetNew(rn.right)
        case _ =>
      }
      r.isNew = false
      r.visited = false
    }

    packTree(oldTopNode)
    packagedTree += EndOfTreeInPackagedProof
    packagedTree ++= directions

    // prepare for the next time proof
    resetNew(topNode)
    directions = new mutable.ArrayBuffer[Byte]
    directionsBitLength = 0
    oldTopNode = topNode

    SerializedAdProof @@ packagedTree.toArray
  }


  /**
    * Walk from tree to a leaf.
    *
    * @param internalNodeFn - function applied to internal nodes. Takes current internal node and current IR, returns
    *                       new internal nod and new IR
    * @param leafFn         - function applied to leafss. Takes current leaf and current IR, returns result of walk LR
    * @param initial        - initial value of IR
    * @tparam IR - result of applying internalNodeFn to internal node. E.g. some accumutalor of previous results
    * @tparam LR - result of applying leafFn to a leaf. Result of all walk application
    * @return
    */
  def treeWalk[IR, LR](internalNodeFn: (InternalProverNode[D], IR) => (ProverNodes[D], IR),
                       leafFn: (ProverLeaf[D], IR) => LR,
                       initial: IR): LR = {
    def walk(rNode: ProverNodes[D], ir: IR): LR = {
      rNode match {
        case leaf: ProverLeaf[D] =>
          leafFn(leaf, ir)

        case r: InternalProverNode[D] =>
          val i = internalNodeFn(r, ir)
          walk(i._1, i._2)
      }
    }

    walk(topNode, initial)
  }


  /**
    *
    * @param rand - source of randomness
    * @return Random leaf from the tree that is not positive or negative infinity
    */
  def randomWalk(rand: Random = new Random): Option[(ADKey, ADValue)] = {
    def internalNodeFn(r: InternalProverNode[D], dummy: Unit): (ProverNodes[D], Unit) =
      rand.nextBoolean() match {
        case true =>
          (r.right, ())
        case false =>
          (r.left, ())
      }

    def leafFn(leaf: ProverLeaf[D], dummy: Unit): Option[(ADKey, ADValue)] = {
      if (leaf.key sameElements PositiveInfinityKey) None
      else if (leaf.key sameElements NegativeInfinityKey) None
      else Some(leaf.key -> leaf.value)
    }

    treeWalk(internalNodeFn, leafFn, ())
  }

  /**
    * A simple non-modifying non-proof-generating lookup.
    * Does not mutate the data structure
    *
    * @return Some(value) for value associated with the given key if key is in the tree, and None otherwise
    */
  def unauthenticatedLookup(key: ADKey): Option[ADValue] = {
    def internalNodeFn(r: InternalProverNode[D], found: Boolean) =
      if (found) {
        // left all the way to the leaf
        (r.left, true)
      } else {
        ByteArray.compare(key, r.key) match {
          case 0 => // found in the tree -- go one step right, then left to the leaf
            (r.right, true)
          case o if o < 0 => // going left, not yet found
            (r.left, false)
          case _ => // going right, not yet found
            (r.right, false)
        }
      }

    def leafFn(leaf: ProverLeaf[D], found: Boolean): Option[ADValue] =
      if (found) Some(leaf.value) else None

    treeWalk(internalNodeFn, leafFn, false)
  }


  /*
  def unauthenticatedLookup(key: ADKey): Option[ADValue] = {
    def unauthenticatedLookupHelper(rNode: ProverNodes[D], found: Boolean): Option[ADValue] = {
      rNode match {
        case leaf: ProverLeaf[D] =>
          if (found) Some(leaf.value) else None

        case r: InternalProverNode[D] =>
          if (found) {
            // left all the way to the leaf
            unauthenticatedLookupHelper(r.left, found = true)
          } else {
            ByteArray.compare(key, r.key) match {
              case 0 => // found in the tree -- go one step right, then left to the leaf
                unauthenticatedLookupHelper(r.right, found = true)
              case o if o < 0 => // going left, not yet found
                unauthenticatedLookupHelper(r.left, found = false)
              case _ => // going right, not yet found
                unauthenticatedLookupHelper(r.right, found = false)
            }
          }
      }
    }
    unauthenticatedLookupHelper(topNode, found = false)
  }*/

  /**
    * Is for debug only
    *
    * Checks the BST order, AVL balance, correctness of leaf positions, correctness of first and last
    * leaf, correctness of nextLeafKey fields
    * If postProof, then also checks for visited and isNew fields being false
    * Warning: slow -- takes linear time in tree size
    * Throws exception if something is wrong
    **/
  private[batch] def checkTree(postProof: Boolean = false): Unit = {
    var fail: Boolean = false

    def checkTreeHelper(rNode: ProverNodes[D]): (ProverLeaf[D], ProverLeaf[D], Int) = {
      def myRequire(t: Boolean, s: String): Unit = {
        if (!t) {
          var x = rNode.key(0).toInt
          if (x < 0) x = x + 256
          log.error("Tree failed at key = " + x + ": " + s)
          fail = true
        }
      }

      myRequire(!postProof || (!rNode.visited && !rNode.isNew), "postproof flags")
      rNode match {
        case r: InternalProverNode[D] =>
          if (r.left.isInstanceOf[InternalProverNode[D]])
            myRequire(ByteArray.compare(r.left.key, r.key) < 0, "wrong left key")
          if (r.right.isInstanceOf[InternalProverNode[D]])
            myRequire(ByteArray.compare(r.right.key, r.key) > 0, "wrong right key")

          val (minLeft, maxLeft, leftHeight) = checkTreeHelper(r.left)
          val (minRight, maxRight, rightHeight) = checkTreeHelper(r.right)
          myRequire(maxLeft.nextLeafKey sameElements minRight.key, "children don't match")
          myRequire(minRight.key sameElements r.key, "min of right subtree doesn't match")
          myRequire(r.balance >= -1 && r.balance <= 1 && r.balance.toInt == rightHeight - leftHeight, "wrong balance")
          val height = math.max(leftHeight, rightHeight) + 1
          (minLeft, maxRight, height)

        case l: ProverLeaf[D] =>
          (l, l, 0)
      }
    }

    val (minTree, maxTree, treeHeight) = checkTreeHelper(topNode)
    require(minTree.key sameElements NegativeInfinityKey)
    require(maxTree.nextLeafKey sameElements PositiveInfinityKey)
    require(treeHeight == rootNodeHeight)

    require(!fail, "Tree failed: \n" + toString)
  }


  override def toString: String = {

    def stringTreeHelper(rNode: ProverNodes[D], depth: Int): String = {
      Seq.fill(depth + 2)(" ").mkString + (rNode match {
        case leaf: ProverLeaf[D] =>
          "At leaf label = " + arrayToString(leaf.label) + " key = " + arrayToString(leaf.key) +
            " nextLeafKey = " + arrayToString(leaf.nextLeafKey) + "\n"
        case r: InternalProverNode[D] =>
          "Internal node label = " + arrayToString(r.label) + " key = " + arrayToString(r.key) + " balance = " +
            r.balance + "\n" + stringTreeHelper(r.left, depth + 1) +
            stringTreeHelper(r.right, depth + 1)
      })
    }

    stringTreeHelper(topNode, 0)
  }
}
