package set

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._

import listspecs.ListSpecs._

object Set {

  def empty[T]: Set[T] = Set(Nil[T]())

  def isSet[T](l: List[T]): Boolean = {
    l == l.unique
  } ensuring {
    res => l match {
      case Nil() => true
      case (x :: xs) => (res ==> isSet(xs)) because {
        tailNotContains(l) && uniqueNotContains(xs, x) && {
          xs                         ==| subCons(xs, x)      |
          (x :: xs) - x              ==| isSet(x :: xs)      |
          (x :: xs).unique - x       ==| trivial             |
          (x :: (xs.unique - x)) - x ==| trivial             |
          (xs.unique - x) - x        ==| subId(xs.unique, x) |
          xs.unique - x              ==| subId(xs.unique, x) |
          xs.unique
        }.qed
      }
    }
  }

  // This set constructor guarantees that the underlying list of the set has the
  // isSet property.
  def set[T](list: List[T]): Set[T] = {
    assert(uniqueIdem(list))
    Set(list.unique)
  }

  def set[T](x: T): Set[T] = {
    set(List(x))
  }

  // If every element of (x :: xs) only occurs once then xs does not contain x.
  def tailNotContains[T](l: List[T]): Boolean = {
    require(isSet(l))

    l match {
      case Nil() => true
      case (x :: xs) => !xs.contains(x)
    }
  }.holds

}

import Set._


case class Set[T](list: List[T]) {
  require(isSet(list))

  // Set union.
  def ++(that: Set[T]): Set[T] = {
    set(this.list ++ that.list)
  }

  // Set element addition.
  def +(x: T): Set[T] = {
    this ++ set(x)
  }

  def -(x: T): Set[T] = {
    set(this.list - x)
  }

  def &(that: Set[T]): Set[T] = {
    this match {
      case (ss + s) =>
        if (that contains s) (ss & that) + s
        else (ss & that)
      case _ => this
    }
  }

  def isEmpty: Boolean = list.isEmpty

  def nonEmpty: Boolean = !isEmpty

  def size: BigInt = list.size

  def contains(x: T): Boolean = list.contains(x)

  def forall(p: T => Boolean): Boolean = list.forall(p)

  def exists(p: T => Boolean): Boolean = list.exists(p)

  def subsetOf(that: Set[T]): Boolean = {
    forall { x => that contains x }
  } // ensuring { _ ==> (this.size <= that.size) }

  def ==(that: Set[T]): Boolean = {
    (this subsetOf that) && (that subsetOf this)
  }

  // def foldRight[U](f: (T, U) => U, z: U): U = set(list foldRight(f, z))

  def map[U](f: T => U): Set[U] = set(list map f)

  def flatMap[U](f: T => Set[U]): Set[U] =
    SetOps.flatten(this map f)

  def filter(p: T => Boolean): Set[T] = {
    this match {
      case (ss + s) if p(s) => ss.filter(p) + s
      case (ss + s) => ss.filter(p)
      case _ => this
    }
  }

  def powerSet: Set[Set[T]] = {
    this match {
      case (xs + x) =>
        val ps = xs.powerSet
        ps ++ ps.map { _ + x }
      case _ => set(this)
    }
  }

}

object SetOps {
  def flatten[T](sets: Set[Set[T]]): Set[T] = {
    sets match {
      case (ss + s) => s ++ flatten(ss)
      case _ => Set.empty
    }
  }
}

object SetSpecs {

  @induct
  def subForall[T](xs: List[T], x: T, p: T => Boolean): Boolean = {
    require(p(x))
    xs.forall(p) == (xs - x).forall(p)
  }.holds

  def uniqueForall[T](xs: List[T], p: T => Boolean): Boolean = {
    xs.forall(p) == xs.unique.forall(p)
  }.holds because {
    xs match {
      case Nil() => trivial
      case (a :: as) => if (p(a)) {
        xs.unique.forall(p)                  ==| trivial                    |
        (a :: (as.unique - a)).forall(p)     ==| trivial                    |
        (p(a) && (as.unique - a).forall(p))  ==| subForall(as.unique, a, p) |
        (p(a) && as.unique.forall(p))        ==| uniqueForall(as, p)        |
        (p(a) && as.forall(p))               ==| trivial                    |
        xs.forall(p)
      }.qed else trivial // FIXME: This shouldn't be needed...
    }
  }

  def unionSubset[T](xs: Set[T], ys: Set[T], zs: Set[T]): Boolean = {
    (xs.subsetOf(zs) && ys.subsetOf(zs)) == (xs ++ ys).subsetOf(zs)
  }.holds because {
    val p = { (x: T) => zs contains x }

    (xs ++ ys).subsetOf(zs)                  ==| trivial |
    (xs ++ ys).forall(p)                     ==| trivial |
    set(xs.list ++ ys.list).list.forall(p)   ==| trivial |
    (xs.list ++ ys.list).unique.forall(p)    ==| uniqueForall(xs.list ++ ys.list, p) |
    (xs.list ++ ys.list).forall(p)           ==| forallAssoc(xs.list, ys.list, p) |
    (xs.list.forall(p) && ys.list.forall(p)) ==| trivial |
    (xs.forall(p) && ys.forall(p))           ==| trivial |
    (xs.subsetOf(zs) && ys.subsetOf(zs))
  }.qed


  def count[T](xs: List[T], x: T): BigInt = {
    xs.filter(_ == x).size
  }

  @induct
  def subCount[T](xs: List[T], x: T): Boolean = {
    count(xs - x, x) == 0
  }.holds

  @induct
  def subCount2[T](xs: List[T], x: T, y: T): Boolean = {
    require(x != y)
    count(xs - x, y) == count(xs, y)
  }.holds

  def uniqueCount[T](xs: List[T], x: T): Boolean = {
    require(xs contains x)
    count(xs.unique, x) == 1
  }.holds because {

    xs match {
      case Nil() => trivial
      case (y :: ys) => {
        if (y == x) {
          count(xs.unique, x)                         ==| trivial                |
          xs.unique.filter(_ == x).size               ==| trivial                |
          (y :: (ys.unique - y)).filter(_ == x).size  ==| (y == x)               |
          (y :: (ys.unique - y).filter(_ == x)).size  ==| trivial                |
          1 + (ys.unique - y).filter(_ == x).size     ==| trivial                |
          1 + count(ys.unique - y, x)                 ==| subCount(ys.unique, x) |
          BigInt(1)
        }.qed else {
          count(xs.unique, x)                         ==| trivial                    |
          xs.unique.filter(_ == x).size               ==| trivial                    |
          (y :: (ys.unique - y)).filter(_ == x).size  ==| (y != x)                   |
          (ys.unique - y).filter(_ == x).size         ==| trivial                    |
          count(ys.unique - y, x)                     ==| subCount2(ys.unique, y, x) |
          count(ys.unique, x)                         ==| uniqueCount(ys, x)         |
          BigInt(1)
        }
      }.qed
    }
  }

  def uniqueSubSize[T](xs: List[T], z: T): Boolean = {
    require(xs contains z)
    xs.unique.size == 1 + (xs.unique - z).size
  }.holds // because {
  //   xs match {
  //     case (y :: Nil()) => {
  //       assert(y == z)

  //       xs.unique.size                  ==| trivial  |
  //       (y :: (Nil().unique - y)).size  ==| trivial  |
  //       (y :: Nil()).size               ==| trivial  |
  //       BigInt(1)                       ==| trivial  |
  //       1 + (List(z).unique - z).size   ==| (y == z) |
  //       1 + (xs.unique - z).size
  //     }.qed
  //     case (y :: ys) => if (z == y) {
  //       xs.unique.size               ==| trivial              |
  //       (y :: (ys.unique - y)).size  ==| trivial              |
  //       1 + (ys.unique - y).size     ==| subUniqueComm(ys, y) |
  //       1 + (ys - y).unique.size     ==| (z == y)             |
  //       1 + (xs - z).unique.size     ==| subUniqueComm(xs, z) |
  //       1 + (xs.unique - z).size
  //     }.qed else {
  //       xs.unique.size                         ==| trivial                  |
  //       (y :: (ys.unique - y)).size            ==| trivial                  |
  //       1 + (ys.unique - y).size               ==| subUniqueComm(ys, y)     |
  //       1 + (ys - y).unique.size               ==| uniqueSubSize(ys - y, z) |
  //       2 + ((ys - y).unique - z).size         //==| subUniqueComm(ys, y)     |
  //       // 2 + ((ys.unique - y) - z).size         //==| trivial                  |
  //       // 1 + (y :: ((ys.unique - y) - z)).size  ==| (y != z)                 |
  //       // 1 + ((y :: (ys.unique - y)) - z).size  ==| trivial                  |
  //       // 1 + (xs.unique - z).size
  //     }.qed
  //   }
  // }


  @induct
  def subSize[T](xs: List[T], x: T): Boolean = {
    (xs - x).size <= xs.size
  }.holds

  def containsSize[T](xs: Set[T], x: T): Boolean = {
    require(xs contains x)
    (xs - x).size <= xs.size
  }.holds because { subSize(xs.list, x) }

  def subsetOfSize[T](xs: Set[T], ys: Set[T]): Boolean = {
    require(xs subsetOf ys)
    xs.size <= ys.size
  }.holds

}


object + {
  def unapply[T](s: Set[T]): Option[(Set[T], T)] = s.list match {
    case Nil() => None()
    case Cons(x, xs) => Some((set(xs), x))
  }
}

// FIXME: Bug: Stainless doesn't seem to support boolean extractors.
object SNil {
  def unapply[T](s: Set[T]): Boolean = s.list match {
    case Nil() => true
    case _     => false
  }
}

