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
  }

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

