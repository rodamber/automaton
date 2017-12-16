package uset

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._

import USetSpecs._


sealed abstract class USet[T] {

  def forall(p: T => Boolean): Boolean = this match {
    case USNil() => true
    case USCons(x, xs) => p(x) && xs.forall(p)
  }

  def exists(p: T => Boolean): Boolean = !forall(!p(_))

  def contains(x: T): Boolean = exists(_ == x)

  def subsetOf(that: USet[T]): Boolean = forall { that contains _ }

  def same(that: USet[T]): Boolean = this.subsetOf(that) && that.subsetOf(this)

  def nsame(that: USet[T]): Boolean = !same(that)

  def isEmpty: Boolean = this match {
    case USNil() => true
    case _ => false
  }

  def size: BigInt = {
    require(setInv(this))

    this match {
      case USNil() => BigInt(0)
      case USCons(_, xs) => 1 + xs.size
    }
  } ensuring { _ >= 0 }

  def +(y: T): USet[T] = {
    require(setInv(this))

    this match {
      case USNil() =>
        USCons(y, USNil())
      case USCons(x, xs) =>
        if (x == y) {
          this
        } else {
          USCons(x, xs + y)
        }
    }
  } // ensuring { setInv(_) }

  def ++(that: USet[T]): USet[T] = {
    require(setInv(this) && setInv(that))
    decreases(size + 1)

    this match {
      case USNil() => that
      case USCons(x, xs) =>
        assert(addInv(xs ++ that, x))
        assert(xs.size < size)

        (xs ++ that) + x
    }
  } ensuring { setInv(_) }

  def -(y: T): USet[T] = {
    require(setInv(this))

    this match {
      case USNil() => USNil()
      case USCons(x, xs) =>
        if (x == y) xs
        else USCons(x, xs - y)
    }
  } // ensuring { setInv(_) }

  def --(that: USet[T]): USet[T] = {
    require(setInv(this) && setInv(that))
    decreases(that.size + 1)

    that match {
      case USNil() => this
      case USCons(y, ys) =>
        assert(subInv(this -- ys, y))
        assert(ys.size < that.size)

        (this -- ys) - y
    }
  } ensuring { setInv(_) }

}

case class USCons[T](x: T, xs: USet[T]) extends USet[T]
case class USNil[T]() extends USet[T]


object USetSpecs {

  // Set invariant
  def setInv[T](set: USet[T]): Boolean = set match {
    case USNil() => true
    case USCons(x, xs) => !xs.contains(x) && setInv(xs)
  }

  @induct
  def addContains[T](set: USet[T], y: T, z: T): Boolean = {
    require(setInv(set))
    (set + y).contains(z) == (set.contains(z) || y == z)
  }.holds

  def addInv[T](set: USet[T], y: T): Boolean = {
    require(setInv(set))
    setInv(set + y)
  }.holds because {
    set match {
      case USNil() => trivial
      case USCons(x, xs) => if (x == y) {
        trivial
      } else {
        setInv(set + y)                           ==| trivial              |
        setInv(USCons(x, xs + y))                 ==| trivial              |
        (!(xs + y).contains(x) && setInv(xs + y)) ==| addInv(xs, y)        |
        !(xs + y).contains(x)                     ==| addContains(xs, y, x)|
        !(xs.contains(x) || y == x)               ==| trivial              |
        true
      }.qed
    }
  }

  @induct
  def addForall[T](set: USet[T], x: T, p: T => Boolean): Boolean = {
    require(setInv(set))
    (set + x).forall(p) == (set.forall(p) && p(x))
  }.holds

  def unionSubset[T](set1: USet[T], set2: USet[T], set3: USet[T]): Boolean = {
    require(setInv(set1) && setInv(set2))
    (set1.subsetOf(set3) && set2.subsetOf(set3)) ==
      (set1 ++ set2).subsetOf(set3)
  }.holds because {
    set1 match {
      case USNil() => trivial
      case USCons(x, xs) => {
        (set1 ++ set2).subsetOf(set3)                     ==| trivial |
        ((xs ++ set2) + x).subsetOf(set3)                 ==| trivial |
        ((xs ++ set2) + x).forall(set3 contains _)        ==|
          addForall((xs ++ set2), x, (y: T) => set3 contains y) |
        ((xs ++ set2).forall(set3 contains _) &&
           set3.contains(x))                              ==| trivial |
        ((xs ++ set2).subsetOf(set3) && set3.contains(x)) ==| unionSubset(xs, set2, set3) |
        (xs.subsetOf(set3) && set3.contains(x) &&
           set2.subsetOf(set3))                           ==| trivial |
        (set1.subsetOf(set3) && set2.subsetOf(set3))
      }.qed
    }
  }

  def subsetTail[T](set: USet[T]): Boolean = {
    set match {
      case USNil() => true
      case USCons(x, xs) => xs.subsetOf(set)
    }
  }.holds

  def subsetOfId[T](set: USet[T]): Boolean = {
    set.subsetOf(set)
  }.holds because {
    set match {
      case USNil() => trivial
      case USCons(x, xs) => {
        val p = (y: T) => set.contains(y)

        set.subsetOf(set)                      ==| trivial |
        set.forall(p)                          ==| trivial |
        ((set contains x) && (xs forall p))    ==| subsetTail(set) |
        true
      }.qed
    }
  }

  def unionSubset2[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(setInv(set1) && setInv(set2))
    set1.subsetOf(set1 ++ set2) && set2.subsetOf(set1 ++ set2)
  }.holds because { unionSubset(set1, set2, set1 ++ set2) && subsetOfId(set1 ++ set2) }

  @induct
  def subContains[T](set: USet[T], y: T, z: T): Boolean = {
    require(setInv(set) && y != z)
    (set - y).contains(z) == set.contains(z)
  }.holds

  def subInv[T](set: USet[T], y: T): Boolean = {
    require(setInv(set))
    setInv(set - y)
  }.holds because {
    set match {
      case USNil() => trivial
      case USCons(x, xs) => if (x == y) {
        trivial
      } else {
        setInv(set - y)                           ==| trivial               |
        setInv(USCons(x, xs - y))                 ==| trivial               |
        (!(xs - y).contains(x) && setInv(xs - y)) ==| subInv(xs, y)         |
        !(xs - y).contains(x)                     ==| subContains(xs, y, x) |
        !xs.contains(x)
      }.qed
    }
  }

  @induct
  def subSize[T](set: USet[T], y: T): Boolean = {
    require(setInv(set) && set.contains(y))
    (set - y).size == set.size - 1
  }.holds because { subInv(set, y) }

  def subSubContains[T](set1: USet[T], set2: USet[T], z: T): Boolean = {
    require(setInv(set1) && setInv(set2) && set1.contains(z) &&
              !set2.contains(z))
    (set1 -- set2).contains(z)
  }.holds because {
    set2 match {
      case USNil() => trivial
      case USCons(y, ys) => {
        (set1 -- set2).contains(z)     ==| trivial                       |
        ((set1 -- ys) - y).contains(z) ==| subContains(set1 -- ys, y, z) |
        (set1 -- ys).contains(z)       ==| subSubContains(set1, ys, z)   |
        true
      }.qed
    }
  }

  def subSubSize[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(setInv(set1) && setInv(set2) && set2.subsetOf(set1))
    (set1 -- set2).size == set1.size - set2.size
  }.holds because {
    set2 match {
      case USNil() => trivial
      case USCons(y, ys) => {
        assert((set1 -- ys).contains(y) because subSubContains(set1, ys, y))

        (set1 -- set2).size     ==| trivial                 |
        ((set1 -- ys) - y).size ==| subSize(set1 -- ys, y)  |
        (set1 -- ys).size - 1   ==| subSubSize(set1, ys)    |
        set1.size - ys.size - 1 ==| trivial                 |
        set1.size - set2.size
      }.qed
    }
  }

  def sizeSubsetOf[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(setInv(set1) && setInv(set2) && set1.subsetOf(set2))
    set1.size <= set2.size
  }.holds because { subSubSize(set2, set1) }

  def sizeEq[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(setInv(set1) && setInv(set2) && set1.same(set2))
     set1.size == set2.size
  }.holds because { sizeSubsetOf(set1, set2) && sizeSubsetOf(set2, set1) }

  def sizeStrictSubsetOf[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(setInv(set1) && setInv(set2) && set1.subsetOf(set2) && set1.nsame(set2))
    set1.size < set2.size
  }.holds because { sizeSubsetOf(set1, set2) && sizeEq(set1, set2) }

}

