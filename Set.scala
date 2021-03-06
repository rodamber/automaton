package set

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._

import uset._
import uset.USetSpecs._

object Set {
  def apply[T](x: T): Set[T] = Set(USCons(x, USNil()))
  def apply[T](): Set[T] = Set(USNil[T]())
}

object + {
  def unapply[T](set: Set[T]): Option[(T, Set[T])] = set.uset match {
    case USNil() => None()
    case USCons(x, xs) => Some((x, Set(xs)))
  }
}

// FIXME: Stainless doesn't seem to support this
// object Empty {
//   def unapply[T](set: Set[T]): Boolean = set.uset match {
//     case USNil() => true
//     case _ => false
//   }
// }

case class Set[T](uset: USet[T]) {
  require(USetSpecs.setInvariant(uset))

  def contains(x: T): Boolean = uset.contains(x)

  def subsetOf(that: Set[T]): Boolean = uset.subsetOf(that.uset)

  def strictSubsetOf(that: Set[T]): Boolean = uset.strictSubsetOf(that.uset)

  def same(that: Set[T]): Boolean = this.uset.same(that.uset)

  def exists(p: T => Boolean): Boolean = uset.exists(p)

  def size: BigInt = { uset.size } ensuring { _ >= 0 }

  def ++(that: Set[T]): Set[T] = Set(this.uset ++ that.uset)
}

object SetSpecs {

  def sameRefl[T](set: Set[T]): Boolean = {
    set same set
  }.holds because USetSpecs.subsetRefl(set.uset)

  def sameTrans[T](set1: Set[T], set2: Set[T], set3: Set[T]): Boolean = {
    require(set1.same(set2) && set2.same(set3))
    set1 same set3
  }.holds because USetSpecs.sameTrans(set1.uset, set2.uset, set3.uset)

  def sameExists[T](set1: Set[T], set2: Set[T], p: T => Boolean): Boolean = {
    require(set1 same set2)
    set1.exists(p) == set2.exists(p)
  }.holds because USetSpecs.sameExists(set1.uset, set2.uset, p)

  def unionOfSubsetsIsSubset[T](set1: Set[T], set2: Set[T], set3: Set[T]): Boolean = {
    (set1.subsetOf(set3) && set2.subsetOf(set3)) == (set1 ++ set2).subsetOf(set3)
  }.holds because USetSpecs.unionOfSubsetsIsSubset(set1.uset, set2.uset, set3.uset)

  def subsetOfUnion[T](set1: Set[T], set2: Set[T]): Boolean = {
    set1.subsetOf(set1 ++ set2) && set2.subsetOf(set1 ++ set2)
  }.holds because USetSpecs.subsetOfUnion(set1.uset, set2.uset)

  def subsetIsSmallerOrEqual[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(set1 subsetOf set2)
    set1.size <= set2.size
  }.holds because USetSpecs.subsetIsSmallerOrEqual(set1.uset, set2.uset)

  def strictSubsetIsSmaller[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(set1.subsetOf(set2) && set1.strictSubsetOf(set2))
    set1.size < set2.size
  }.holds because USetSpecs.strictSubsetIsSmaller(set2.uset, set1.uset)

}

