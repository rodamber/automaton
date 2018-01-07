package uset

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._

import USetOps._
import USetSpecs._

sealed abstract class USet[T] {

  def contains(x: T): Boolean = this match {
    case USNil() => false
    case USCons(y, ys) => (x == y) || ys.contains(x)
  }

  def subsetOf(that: USet[T]): Boolean = this match {
    case USNil() => true
    case USCons(x, xs) => that.contains(x) && xs.subsetOf(that)
  }

  def strictSubsetOf(that: USet[T]): Boolean =
    subsetOf(that) && !that.subsetOf(this)

  def same(that: USet[T]): Boolean = this.subsetOf(that) && that.subsetOf(this)

  def nsame(that: USet[T]): Boolean = !same(that)

  def isEmpty: Boolean = this match {
    case USNil() => true
    case _ => false
  }

  def nonEmpty: Boolean = !isEmpty

  def exists(p: T => Boolean): Boolean = this match {
    case USNil() => false
    case USCons(x, xs) => p(x) || xs.exists(p)
  }

  def forall(p: T => Boolean): Boolean = this match {
    case USNil() => true
    case USCons(x, xs) => p(x) && xs.forall(p)
  }

  def size: BigInt = {
    require(setInvariant(this))

    this match {
      case USNil() => BigInt(0)
      case USCons(_, xs) => 1 + xs.size
    }
  } ensuring { _ >= 0 }

  def +(y: T): USet[T] = {
    require(setInvariant(this))

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
  } // ensuring { setInvariant(_) }

  def ++(that: USet[T]): USet[T] = {
    require(setInvariant(this) && setInvariant(that))
    decreases(size + 1)

    this match {
      case USNil() => that
      case USCons(x, xs) =>
        assert(addIsSound(xs ++ that, x))
        assert(xs.size < size)

        (xs ++ that) + x
    }
  } ensuring { setInvariant(_) }

  def -(y: T): USet[T] = {
    require(setInvariant(this))

    this match {
      case USNil() => USNil()
      case USCons(x, xs) =>
        if (x == y) xs
        else USCons(x, xs - y)
    }
  } // ensuring { setInvariant(_) }

  def --(that: USet[T]): USet[T] = {
    require(setInvariant(this) && setInvariant(that))
    decreases(that.size + 1)

    that match {
      case USNil() => this
      case USCons(y, ys) =>
        assert(subIsSound(this -- ys, y))
        assert(ys.size < that.size)

        (this -- ys) - y
    }
  } ensuring { setInvariant(_) }

  def powerSet: USet[USet[T]] = {
    require(setInvariant(this))

    this match {
      case USNil() => USCons(USNil(), USNil())
      case USCons(x, xs) =>
        val ps = xs.powerSet

        assert(powerSetIsSound(xs))
        assert(powerSetAllSound(xs))
        assert(mapAddIsSound(ps, x))

        // ps ++ ps.map(_ + x)
        ps ++ mapAdd(ps, x)
    }
  } // ensuring { (res: USet[USet[T]]) => setInvariant(res) }

    def map[R](f: T => R): USet[R] = {
    require(setInvariant(this))

    this match {
      case USNil() => USNil()
      case USCons(x, xs) =>
        val m = xs.map(f)

        assert(addIsSound(m, f(x)))
        m + f(x)
    }
  } // ensuring { (res: USet[R]) => setInvariant(res) }

  def foldLeft[R](z: R)(f: (R,T) => R): R = {
    this match {
      case USNil() => z
      case USCons(x, xs) => xs.foldLeft(f(z, x))(f)
    }
  }


}

case class USCons[T](x: T, xs: USet[T]) extends USet[T]
case class USNil[T]() extends USet[T]

object USetOps {

  def mapAdd[T](sets: USet[USet[T]], x: T): USet[USet[T]] = {
    require(sets.forall((s: USet[T]) => setInvariant(s) && !s.contains(x)) && setInvariant(sets))

    sets match {
      case USNil() => USNil()
      case USCons(s, ss) =>
        assert(setInvariant(ss))
        USCons(s + x, mapAdd(ss, x))
    }
  } // ensuring { (res: USet[USet[T]]) => setInvariant(res) }

}

object USetSpecs {

  def setInvariant[T](set: USet[T]): Boolean = set match {
    case USNil() => true
    case USCons(x, xs) => !xs.contains(x) && setInvariant(xs)
  }

  // ---------------------------------------------------------------------------
  // +

  @induct
  def containsDistAdd[T](set: USet[T], y: T, z: T): Boolean = {
    require(setInvariant(set))
    (set + y).contains(z) == (set.contains(z) || y == z)
  }.holds

  def addIsSound[T](set: USet[T], y: T): Boolean = {
    require(setInvariant(set))
    setInvariant(set + y)
  }.holds because {
    set match {
      case USNil() => trivial
      case USCons(x, xs) => if (x == y) {
        trivial
      } else {
        setInvariant(set + y)                           ==| trivial                   |
        setInvariant(USCons(x, xs + y))                 ==| trivial                   |
        (!(xs + y).contains(x) && setInvariant(xs + y)) ==| addIsSound(xs, y)         |
        !(xs + y).contains(x)                           ==| containsDistAdd(xs, y, x) |
        !(xs.contains(x) || y == x)                     ==| trivial                   |
        true
      }.qed
    }
  }

  @induct
  def addExists[T](set: USet[T], x: T, p: T => Boolean): Boolean = {
    require(setInvariant(set))
    (set + x).exists(p) == (p(x) || set.exists(p))
  }.holds

  @induct
  def addId[T](set: USet[T], x: T): Boolean = {
    require(setInvariant(set) && set.contains(x))
    (set + x) == set
  }.holds

  // ---------------------------------------------------------------------------
  // -

  @induct
  def subContains1[T](set: USet[T], y: T, z: T): Boolean = {
    require(setInvariant(set) && y != z)
    (set - y).contains(z) == set.contains(z)
  }.holds

  def subIsSound[T](set: USet[T], y: T): Boolean = {
    require(setInvariant(set))
    setInvariant(set - y)
  }.holds because {

    set match {
      case USNil() => trivial
      case USCons(x, xs) => if (x == y) {
        trivial
      } else {
        setInvariant(set - y)                           ==| trivial                |
          setInvariant(USCons(x, xs - y))                 ==| trivial                |
          (!(xs - y).contains(x) && setInvariant(xs - y)) ==| subIsSound(xs, y)      |
          !(xs - y).contains(x)                           ==| subContains1(xs, y, x) |
          !xs.contains(x)
      }.qed
    }
  }

  // ---------------------------------------------------------------------------
  // subsetOf

  def subsetRefl[T](set: USet[T]): Boolean = {
    set subsetOf set
  }.holds because {
    set match {
      case USNil() => trivial
      case USCons(x, xs) => set.contains(x) && subsetTail(set)
    }
  }

  def subsetTail[T](set: USet[T]): Boolean = {
    set match {
      case USNil() => true
      case USCons(x, xs) => xs.subsetOf(set)
    }
  }.holds

  def subsetTrans[T](set1: USet[T], set2: USet[T], set3: USet[T]): Boolean = {
    require(set1.subsetOf(set2) && set2.subsetOf(set3))
    set1 subsetOf set3
  }.holds

  def subsetExists[T](set1: USet[T], set2: USet[T], p: T => Boolean): Boolean = {
    require(setInvariant(set1) && setInvariant(set2) &&
              set1.subsetOf(set2) && set1.exists(p))
    set2.exists(p)
  }.holds because {
    set1 match {
      case USNil() => trivial
      case USCons(x, xs) => if (p(x)) {
        set1.exists(p)           ==| trivial |
          p(x)                     ==| trivial |
          (p(x) || set2.exists(p)) ==| addExists(set2, x, p) |
          (set2 + x).exists(p)     ==| addId(set2, x)        |
          set2.exists(p)
      } else {
        set1.exists(p) ==| trivial                   |
          xs.exists(p)   ==| subsetExists(xs, set2, p) |
          set2.exists(p)
      }
    }
  }.qed

  // ---------------------------------------------------------------------------
  // same

  def sameRefl[T](set: USet[T]): Boolean = {
    set same set
  }.holds because subsetRefl(set)

  def sameTrans[T](set1: USet[T], set2: USet[T], set3: USet[T]): Boolean = {
    require(set1.same(set2) && set2.same(set3))
    set1 same set3
  }.holds because { subsetTrans(set1, set2, set3) && subsetTrans(set3, set2, set1) }

  def sameSymm[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(set1 same set2)
    set2 same set1
  }.holds

  def sameExists[T](set1: USet[T], set2: USet[T], p: T => Boolean): Boolean = {
    require(setInvariant(set1) && setInvariant(set2) && set1.same(set2))
    set1.exists(p) == set2.exists(p)
  }.holds because {
    if (set1.exists(p))      subsetExists(set1, set2, p)
    else if (set2.exists(p)) subsetExists(set2, set1, p)
    else                     trivial
  }

  // ---------------------------------------------------------------------------
  // subset, + and ++ (union)

  def subsetOfUnion[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(setInvariant(set1) && setInvariant(set2))
    set1.subsetOf(set1 ++ set2) && set2.subsetOf(set1 ++ set2)
  }.holds because { unionOfSubsetsIsSubset(set1, set2, set1 ++ set2) && subsetRefl(set1 ++ set2) }

  def unionOfSubsetsIsSubset[T](set1: USet[T], set2: USet[T], set3: USet[T]): Boolean = {
    require(setInvariant(set1) && setInvariant(set2))
    (set1.subsetOf(set3) && set2.subsetOf(set3)) == (set1 ++ set2).subsetOf(set3)
  }.holds because {
    set1 match {
      case USNil() => trivial
      case USCons(x, xs) => {
        (set1 ++ set2).subsetOf(set3)                     ==| trivial                                |
        ((xs ++ set2) + x).subsetOf(set3)                 ==| subsetAdd(xs ++ set2, set3, x)         |
        ((xs ++ set2).subsetOf(set3) && set3.contains(x)) ==| unionOfSubsetsIsSubset(xs, set2, set3) |
        (set1.subsetOf(set3) && set2.subsetOf(set3))
      }.qed
    }
  }

  @induct
  def subsetAdd[T](set1: USet[T], set2: USet[T], x: T): Boolean = {
    require(setInvariant(set1))
    (set1 + x).subsetOf(set2) == (set1.subsetOf(set2) && set2.contains(x))
  }.holds

  // ---------------------------------------------------------------------------
  // contains

  @induct
  def tailContains[T](set: USet[T], y: T): Boolean = {
    require(setInvariant(set) && set.contains(y))

    set match {
      case USNil() => true
      case USCons(x, xs) =>
        if (x == y) true
        else xs.contains(y)
    }
  }.holds

  def diffContains[T](set1: USet[T], set2: USet[T], z: T): Boolean = {
    require(setInvariant(set1) && setInvariant(set2) && set1.contains(z) && !set2.contains(z))
    (set1 -- set2).contains(z)
  }.holds because {
    set2 match {
      case USNil() => trivial
      case USCons(y, ys) => {
        (set1 -- set2).contains(z)     ==| trivial                        |
        ((set1 -- ys) - y).contains(z) ==| subContains1(set1 -- ys, y, z) |
        (set1 -- ys).contains(z)       ==| diffContains(set1, ys, z)      |
        true
      }.qed
    }
  }

  // ---------------------------------------------------------------------------
  // size

  @induct
  def subDecSize[T](set: USet[T], y: T): Boolean = {
    require(setInvariant(set) && set.contains(y))
    assert(subIsSound(set, y))

    (set - y).size == set.size - 1
  }.holds because tailContains(set, y)

  def diffSubsetSize[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(setInvariant(set1) && setInvariant(set2) && set2.subsetOf(set1))
    (set1 -- set2).size == set1.size - set2.size
  }.holds because {
    set2 match {
      case USNil() => trivial
      case USCons(y, ys) => {
        assert((set1 -- ys).contains(y) because diffContains(set1, ys, y))

        (set1 -- set2).size     ==| trivial                   |
        ((set1 -- ys) - y).size ==| subDecSize(set1 -- ys, y) |
        (set1 -- ys).size - 1   ==| diffSubsetSize(set1, ys)  |
        set1.size - ys.size - 1 ==| trivial                   |
        set1.size - set2.size
      }.qed
    }
  }

  def subsetIsSmallerOrEqual[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(setInvariant(set1) && setInvariant(set2) && set1.subsetOf(set2))
    set1.size <= set2.size
  }.holds because { diffSubsetSize(set2, set1) }

  def strictSubsetIsSmaller[T](set1: USet[T], set2: USet[T]): Boolean = {
    require(setInvariant(set1) && setInvariant(set2) && set1.strictSubsetOf(set2))
    set1.size < set2.size
  }.holds // because { subsetIsSmallerOrEqual(set1, set2) && sizeEq(set1, set2) }

  // ---------------------------------------------------------------------------
  // map

  def mapIsSound[T,R](set: USet[T], f: T => R): Boolean = {
    require(setInvariant(set))
    setInvariant(set map f)
  }.holds

  def mapAddIsSound[T](sets: USet[USet[T]], x: T): Boolean = {
    require(sets.forall((s: USet[T]) => setInvariant(s) && !s.contains(x)) && setInvariant(sets))

    val m = mapAdd(sets, x)
    m.forall(setInvariant(_)) && setInvariant(m)
  }.holds

  // ---------------------------------------------------------------------------
  // powerSet

  def powerSetIsSound[T](set: USet[T]): Boolean = {
    require(setInvariant(set))
    setInvariant(set.powerSet)
  }.holds

  def powerSetAllSound[T](set: USet[T]): Boolean = {
    require(setInvariant(set))
    set.powerSet.forall(setInvariant(_))
  }.holds

  def powerSetSubset[T](x: USet[T], y: USet[T]): Boolean = {
    require(setInvariant(x) && setInvariant(y))
    x.powerSet.contains(y) == y.subsetOf(x)
  }.holds

  //




}

