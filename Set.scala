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

  def same(that: Set[T]): Boolean = this.uset.same(that.uset)

  def nsame(that: Set[T]): Boolean = this.uset.nsame(that.uset)

  def isEmpty: Boolean = uset.isEmpty

  def nonEmpty: Boolean = uset.nonEmpty

  def exists(p: T => Boolean): Boolean = uset.exists(p)

  def forall(p: T => Boolean): Boolean = uset.forall(p)

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

  def powerSet: Set[Set[T]] = {
    val ups: USet[USet[T]] = uset.powerSet

    assert(USetSpecs.powerSetAllSound(uset))
    assert(USetSpecs.powerSetIsSound(uset))

    // Implied by the previous assertion.
    assert(USetSpecs.setInvariant(ups))

    // FIXME: I must be missing something here. Stainless tells me that the
    // previous assertion is true. However, it also tells me that the call
    // precondition for mapIsSound may be violated...
    assert(mapIsSound(ups, (us: USet[T]) => {
                        assert(USetSpecs.setInvariant(us))
                        Set(us)
                      }))

    Set(ups.map(Set(_)))
  }

  def map[R](f: T => R): Set[R] = Set(uset map f)

  def *[U](that: Set[U]): Set[(T, U)] = Set(uset * that.uset)

  def foldLeft[R](z: R)(f: (R,T) => R): R = uset.foldLeft(z)(f)

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
  // same

  def sameRefl[T](set: Set[T]): Boolean = {
    set same set
  }.holds because USetSpecs.sameRefl(set.uset)

  def sameTrans[T](set1: Set[T], set2: Set[T], set3: Set[T]): Boolean = {
    require(set1.same(set2) && set2.same(set3))
    set1 same set3
  }.holds because USetSpecs.sameTrans(set1.uset, set2.uset, set3.uset)

  def sameSymm[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(set1 same set2)
    set2 same set1
  }.holds because USetSpecs.sameSymm(set1.uset, set2.uset)

  def sameExists[T](set1: Set[T], set2: Set[T], p: T => Boolean): Boolean = {
    require(set1 same set2)
    set1.exists(p) == set2.exists(p)
  }.holds because USetSpecs.sameExists(set1.uset, set2.uset, p)

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

  // ---------------------------------------------------------------------------
  // powerSet

  def powerSetSubset[T](x: Set[T], y: Set[T]): Boolean = {
    x.powerSet.contains(y) == y.subsetOf(x)
  }.holds because USetSpecs.powerSetSubset(x.uset, y.uset)

  // ---------------------------------------------------------------------------
  // *

  def prodContains[T,U](ts: Set[T], us: Set[U], x: T, y: U): Boolean = {
    (ts.contains(x) && us.contains(y)) == (ts * us).contains(x -> y)
  }.holds because USetSpecs.prodContains(ts.uset, us.uset, x, y)

  // ---------------------------------------------------------------------------
  // forall

  def forallContains[T](set: Set[T], x: T, p: T => Boolean): Boolean = {
    require(set.contains(x) && set.forall(p))
    p(x)
  }.holds because USetSpecs.forallContains(set.uset, x, p)

}
