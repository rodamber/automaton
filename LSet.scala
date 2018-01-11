package crazy

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => SSet, _}
import stainless.proof._

import set.{Set => MSet, _}
import SetSpecs._

case class Set[T](uset: SSet[T], // stainless set
                   myset: MSet[T]) {
  // require(invariant(uset, myset))

  def contains(x: T): Boolean = 
    uset.contains(x)

  def subsetOf(that: Set[T]): Boolean = 
    uset.subsetOf(that.uset)

  def strictSubsetOf(that: Set[T]): Boolean = 
    uset.subsetOf(that.uset) && uset != that.uset

  def exists(p: T => Boolean): Boolean = 
    myset.exists(p)

  def ++(that: Set[T]): Set[T] = 
    Set(this.uset ++ that.uset, this.myset ++ that.myset)

  def size: BigInt = { 
    myset.size
  } ensuring { _ >= 0 }

}

object SetSpecs {

  def invariant[T](uset: SSet[T], myset: MSet[T]): Boolean = {
    forall { (x: T) => uset.contains(x) == myset.contains(x) }
  }

  def invnil[T]: Boolean = {
    invariant(SSet.empty, MSet())
  }.holds

  // // $ stainless --timeout=10 --verification --watch --vc-cache SetProps.scala Set.scala USet.scala --termination --functions=invsingleton
  // // [Warning ] Parallelism is disabled.
  // // [ Error  ] invsingleton$0 depends on missing dependencies: apply$3.
  // // [Internal] Missing some nodes in Registry: apply$3
  // // [Internal] Please inform the authors of Inox about this message
  // // [Internal] inox.package$FatalError: Missing some nodes in Registry: apply$3
  // // [Internal] Please inform the authors of Inox about this message
  // def invsingleton[T](x: T): Boolean = {
  //   import uset._
  //   invariant(SSet(x), Set(USCons(x, USNil())))
  // }.holds

}
