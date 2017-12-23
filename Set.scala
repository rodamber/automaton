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

  def size: BigInt = { uset.size } ensuring { _ >= 0 }

  def contains(x: T): Boolean = uset.contains(x)

  def subsetOf(that: Set[T]): Boolean = uset.subsetOf(that.uset)

  def strictSubsetOf(that: Set[T]): Boolean = uset.strictSubsetOf(that.uset)

  def eq(that: Set[T]): Boolean = this.uset.eq(that.uset)

  def neq(that: Set[T]): Boolean = this.uset.neq(that.uset)

  def isEmpty: Boolean = uset.isEmpty

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

  def unionOfSubsetsIsSubset[T](set1: Set[T], set2: Set[T], set3: Set[T]): Boolean = {
    (set1.subsetOf(set3) && set2.subsetOf(set3)) == (set1 ++ set2).subsetOf(set3)
  }.holds because { USetSpecs.unionOfSubsetsIsSubset(set1.uset, set2.uset, set3.uset) }

  def subsetIsSmallerOrEqual[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(set1 subsetOf set2)
    set1.size <= set2.size
  }.holds because { USetSpecs.subsetIsSmallerOrEqual(set1.uset, set2.uset) }

  def strictSubsetIsSmaller[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(set1.subsetOf(set2) && set1.strictSubsetOf(set2))
    set1.size < set2.size
  }.holds because { USetSpecs.strictSubsetIsSmaller(set1.uset, set2.uset) }

}

