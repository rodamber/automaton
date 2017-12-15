package set

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._


sealed abstract class Set[T] {

  import SetSpecs._

  def size: BigInt = {
    this match {
      case SNil() => BigInt(0)
      case SCons(_, xs) => 1 + xs.size
    }
  } ensuring { _ >= 0 }

  def forall(p: T => Boolean): Boolean = this match {
    case SNil() => true
    case SCons(x, xs) => p(x) && xs.forall(p)
  }

  def exists(p: T => Boolean): Boolean = this match {
    case SNil() => false
    case SCons(x, xs) => p(x) || xs.exists(p)
  }

  def contains(x: T): Boolean = exists(_ == x)

  def subsetOf(ys: Set[T]): Boolean = forall { ys contains _ }

  def +(y: T): Set[T] = {
    require(setInv(this))

    this match {
      case SNil() =>
        SCons(y, SNil())
      case SCons(x, xs) =>
        if (x == y) {
          this
        } else {
          SCons(x, xs + y)
        }
    }
  } // ensuring { setInv(_) }

  def ++(that: Set[T]): Set[T] = {
    require(setInv(this) && setInv(that))
    decreases(size + 1)

    this match {
      case SNil() => that
      case SCons(x, xs) =>
        assert(addInv(xs ++ that, x))
        assert(xs.size < size)

        (xs ++ that) + x
    }
  } ensuring { setInv(_) }

  def -(y: T): Set[T] = {
    require(setInv(this))

    this match {
      case SNil() => SNil()
      case SCons(x, xs) =>
        if (x == y) xs
        else SCons(x, xs - y)
    }
  } // ensuring { setInv(_) }

  def --(that: Set[T]): Set[T] = {
    require(setInv(this) && setInv(that))
    decreases(that.size + 1)

    that match {
      case SNil() => this
      case SCons(y, ys) =>
        assert(subInv(this -- ys, y))
        assert(ys.size < that.size)

        (this -- ys) - y
    }
  } ensuring { setInv(_) }

}

case class SCons[T](x: T, xs: Set[T]) extends Set[T]
case class SNil[T]() extends Set[T]

object SetSpecs {

  // Set invariant
  def setInv[T](set: Set[T]): Boolean = set match {
    case SNil() => true
    case SCons(x, xs) => !xs.contains(x) && setInv(xs)
  }

  @induct
  def addContains[T](set: Set[T], y: T, z: T): Boolean = {
    require(setInv(set))
    (set + y).contains(z) == (set.contains(z) || y == z)
  }.holds

  def addInv[T](set: Set[T], y: T): Boolean = {
    require(setInv(set))
    setInv(set + y)
  }.holds because {
    set match {
      case SNil() => trivial
      case SCons(x, xs) => if (x == y) {
        trivial
      } else {
        setInv(set + y)                           ==| trivial              |
        setInv(SCons(x, xs + y))                  ==| trivial              |
        (!(xs + y).contains(x) && setInv(xs + y)) ==| addInv(xs, y)        |
        !(xs + y).contains(x)                     ==| addContains(xs, y, x)|
        !(xs.contains(x) || y == x)               ==| trivial              |
        true
      }.qed
    }
  }

  @induct
  def addForall[T](set: Set[T], x: T, p: T => Boolean): Boolean = {
    require(setInv(set))
    (set + x).forall(p) == (set.forall(p) && p(x))
  }.holds

  def unionSubset[T](set1: Set[T], set2: Set[T], set3: Set[T]): Boolean = {
    require(setInv(set1) && setInv(set2))
    (set1.subsetOf(set3) && set2.subsetOf(set3)) ==
      (set1 ++ set2).subsetOf(set3)
  }.holds because {
    set1 match {
      case SNil() => trivial
      case SCons(x, xs) => {
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

  @induct
  def subContains[T](set: Set[T], y: T, z: T): Boolean = {
    require(setInv(set) && y != z)
    (set - y).contains(z) == set.contains(z)
  }.holds

  def subInv[T](set: Set[T], y: T): Boolean = {
    require(setInv(set))
    setInv(set - y)
  }.holds because {
    set match {
      case SNil() => trivial
      case SCons(x, xs) => if (x == y) {
        trivial
      } else {
        setInv(set - y)                           ==| trivial               |
        setInv(SCons(x, xs - y))                  ==| trivial               |
        (!(xs - y).contains(x) && setInv(xs - y)) ==| subInv(xs, y)         |
        !(xs - y).contains(x)                     ==| subContains(xs, y, x) |
        !xs.contains(x)
      }.qed
    }
  }

  @induct
  def subSize[T](set: Set[T], x: T): Boolean = {
    require(setInv(set) && set.contains(x))
    (set - x).size == set.size - 1
  }.holds

  def subSubContains[T](set1: Set[T], set2: Set[T], z: T): Boolean = {
    require(setInv(set1) && setInv(set2) && set1.contains(z) &&
              !set2.contains(z))
    (set1 -- set2).contains(z)
  }.holds because {
    set2 match {
      case SNil() => trivial
      case SCons(y, ys) => {
        (set1 -- set2).contains(z)     ==| trivial                       |
        ((set1 -- ys) - y).contains(z) ==| subContains(set1 -- ys, y, z) |
        (set1 -- ys).contains(z)       ==| subSubContains(set1, ys, z)   |
        true
      }.qed
    }
  }

  def subSubSize[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(setInv(set1) && setInv(set2) && set2.subsetOf(set1))
    (set1 -- set2).size == set1.size - set2.size
  }.holds because {
    set2 match {
      case SNil() => trivial
      case SCons(y, ys) => {
        assert((set1 -- ys).contains(y) because subSubContains(set1, ys, y))

        (set1 -- set2).size     ==| trivial                 |
        ((set1 -- ys) - y).size ==| subSize(set1 -- ys, y)  |
        (set1 -- ys).size - 1   ==| subSubSize(set1, ys)    |
        set1.size - ys.size - 1 ==| trivial                 |
        set1.size - set2.size
      }.qed
    }
  }

  def sizeSubsetOf[T](set1: Set[T], set2: Set[T]): Boolean = {
    require(setInv(set1) && setInv(set2) && set1.subsetOf(set2))
    set1.size <= set2.size
  }.holds because { subSubSize(set2, set1) }

}
