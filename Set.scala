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

  def eq(that: Set[T]): Boolean = this.uset.eq(that.uset)

  def neq(that: Set[T]): Boolean = this.uset.neq(that.uset)

  def isEmpty: Boolean = uset.isEmpty

  def nonEmpty: Boolean = uset.nonEmpty

  def exists(p: T => Boolean): Boolean = uset.exists(p)

  def size: BigInt = { uset.size } ensuring { _ >= 0 }

  def +(y: T): Set[T] = {
    assert(setInvariant(uset + y) because addIsSound(uset, y))
    Set(uset + y)
  }

  def ++(that: Set[T]): Set[T] = Set(this.uset ++ that.uset)

  def -(y: T): Set[T] = {
    assert(setInvariant(uset - y) because subIsSound(uset, y))
    Set(uset - y)
  }

  def --(that: Set[T]): Set[T] = Set(this.uset -- that.uset)

}

object SetSpecs {

  // ---------------------------------------------------------------------------
  // subsetOf

  def subsetRefl[T](set: Set[T]): Boolean = {
    set.subsetOf(set)
  }.holds because USetSpecs.subsetRefl(set.uset)

  def subsetTrans[T](set1: Set[T], set2: Set[T], set3: Set[T]): Boolean = {
    require(set1.subsetOf(set2) && set2.subsetOf(set3))
    set1 subsetOf set3
  }.holds because USetSpecs.subsetTrans(set1.uset, set2.uset, set3.uset)

  // ---------------------------------------------------------------------------
  // eq

  def eqRefl[T](set: Set[T]): Boolean = {
    set eq set
  }.holds because USetSpecs.eqRefl(set.uset)

  def eqTrans[T](set1: Set[T], set2: Set[T], set3: Set[T]): Boolean = {
    require(set1.eq(set2) && set2.eq(set3))
    set1 eq set3
  }.holds because USetSpecs.eqTrans(set1.uset, set2.uset, set3.uset)

  def eqSymm[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(set1 eq set2)
    set2 eq set1
  }.holds because USetSpecs.eqSymm(set1.uset, set2.uset)

  // ---------------------------------------------------------------------------
  // subsetOf and ++ (union)

  def unionOfSubsetsIsSubset[T](set1: Set[T], set2: Set[T], set3: Set[T]): Boolean = {
    (set1.subsetOf(set3) && set2.subsetOf(set3)) == (set1 ++ set2).subsetOf(set3)
  }.holds because USetSpecs.unionOfSubsetsIsSubset(set1.uset, set2.uset, set3.uset)

  def subsetOfUnion[T](set1: Set[T], set2: Set[T]): Boolean = {
    set1.subsetOf(set1 ++ set2) && set2.subsetOf(set1 ++ set2)
  }.holds because USetSpecs.subsetOfUnion(set1.uset, set2.uset)

  // ---------------------------------------------------------------------------
  // size

  def subsetIsSmallerOrEqual[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(set1 subsetOf set2)
    set1.size <= set2.size
  }.holds because USetSpecs.subsetIsSmallerOrEqual(set1.uset, set2.uset)

  def strictSubsetIsSmaller[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(set1.subsetOf(set2) && set1.strictSubsetOf(set2))
    set1.size < set2.size
  }.holds because USetSpecs.strictSubsetIsSmaller(set1.uset, set2.uset)

}

