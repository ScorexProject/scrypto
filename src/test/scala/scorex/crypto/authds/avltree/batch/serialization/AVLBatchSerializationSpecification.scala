package scorex.crypto.authds.avltree.batch.serialization

import org.scalacheck.{Arbitrary, Gen}
import org.scalatest.PropSpec
import org.scalatest.prop.GeneratorDrivenPropertyChecks
import scorex.crypto.authds.avltree.batch._
import scorex.crypto.authds.{ADKey, ADValue, TwoPartyTests}
import scorex.crypto.hash.{Blake2b256, _}
import scorex.utils.Random

class AVLBatchSerializationSpecification extends PropSpec with GeneratorDrivenPropertyChecks with TwoPartyTests {

  val InitialTreeSize = 1000
  val KL = 26
  val VL = 8
  val HL = 32
  type D = Digest32
  type HF = Blake2b256.type
  implicit val hf: HF = Blake2b256

  def randomKey(size: Int = 32): ADKey = ADKey @@ Random.randomBytes(size)

  def randomValue(size: Int = 32): ADValue = ADValue @@ Random.randomBytes(size)

  private def generateProver(size: Int = InitialTreeSize): BatchAVLProver[D, HF] = {
    val prover = new BatchAVLProver[D, HF](KL, None)
    val keyValues = (0 until size) map { i =>
      (ADKey @@ Blake2b256(i.toString.getBytes("UTF-8")).take(KL), ADValue @@ i.toString.getBytes("UTF-8"))
    }
    keyValues.foreach(kv => prover.performOneOperation(Insert(kv._1, kv._2)))
    prover.generateProof()
    prover
  }

  property("operation serialization") {
    forAll(operationGen) { op =>
      val keyLength = op.key.length
      val valueLength = op match {
        case Insert(k, v) => v.length
        case Update(k, v) => v.length
        case InsertOrUpdate(k, v) => v.length
        case _ => 0
      }
      val randValueBytes = OperationSerializer.toBytes(op, None)
      val randValueRecovered = OperationSerializer.parseBytes(randValueBytes, keyLength, None).get
      OperationSerializer.toBytes(randValueRecovered, None) shouldEqual randValueBytes

      val fixedValueBytes = OperationSerializer.toBytes(op, Some(valueLength))
      val fixedValueRecovered = OperationSerializer.parseBytes(fixedValueBytes, keyLength, Some(valueLength)).get
      OperationSerializer.toBytes(fixedValueRecovered, Some(valueLength)) shouldEqual fixedValueBytes
    }
  }

  property("slice to pieces and combine tree back") {
    forAll(Gen.choose(100, 100000)) { treeSize: Int =>
      whenever(treeSize >= 100) {
        val tree = generateProver(treeSize)
        val height = tree.rootNodeHeight
        val digest = tree.digest
        val serializer = new BatchAVLProverSerializer[D, HF]
        val sliced = serializer.slice(tree)

        val manifestLeftTree = leftTree(sliced._1.oldRootAndHeight._1)
        val subtreeLeftTree = leftTree(sliced._2.head.subtreeTop)

        manifestLeftTree.length should be < height
        manifestLeftTree.last.asInstanceOf[ProxyInternalNode[D]].leftLabel shouldEqual subtreeLeftTree.head.label

        val recovered = serializer.combine(sliced).get
        recovered.digest shouldEqual digest
      }
    }
  }

  property("slice to Array[Byte] pieces and combine tree back") {
    forAll(Gen.choose(100, 100000)) { treeSize: Int =>
      val serializer = new BatchAVLProverSerializer[D, HF]
      val tree = generateProver(treeSize)
      val kl = tree.keyLength
      val digest = tree.digest

      val sliced = serializer.slice(tree)


      val manifestBytes = serializer.manifestToBytes(sliced._1)
      val subtreeBytes = sliced._2.map(t => serializer.subtreeToBytes(t))

      val recoveredManifest = serializer.manifestFromBytes(manifestBytes).get
      val recoveredSubtrees = subtreeBytes.map(b => serializer.subtreeFromBytes(b, kl).get)

      val subtreeBytes2 = recoveredSubtrees.map(t => serializer.subtreeToBytes(t))
      subtreeBytes.flatten shouldEqual subtreeBytes2.flatten

      val recoveredSliced = (recoveredManifest, recoveredSubtrees)
      val recovered = serializer.combine(recoveredSliced).get

      recovered.digest shouldEqual digest
    }
  }

  def leftTree(n: ProverNodes[D]): Seq[ProverNodes[D]] = n match {
    case n: ProxyInternalNode[D] if n.isEmpty =>
      Seq(n)
    case n: InternalProverNode[D] =>
      n +: leftTree(n.left)
    case l: ProverLeaf[D] =>
      Seq(l)
  }


  lazy val operationGen: Gen[Operation] = for {
    tp <- Gen.choose(0, 6)
    key <- Arbitrary.arbitrary[Array[Byte]].map(k => ADKey @@ k)
    value <- Arbitrary.arbitrary[Array[Byte]].map(k => ADValue @@ k)
  } yield {
    tp match {
      case 1 => Lookup(key)
      case 2 => Remove(key)
      case 3 => RemoveIfExists(key)
      case 4 => Insert(key, value)
      case 5 => Update(key, value)
      case 6 => InsertOrUpdate(key, value)
      case _ => UnknownModification
    }
  }

}
