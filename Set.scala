package set

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._


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

  // List.unique does not add elements that weren't already there.
  @induct
  def uniqueNotContains[T](xs: List[T], x: T): Boolean = {
    require(!xs.contains(x))
    !xs.unique.contains(x)
  }.holds

  @induct
  def subCons[T](xs: List[T], x: T): Boolean = {
    require(!xs.contains(x))
    xs == (x :: xs) - x
  }.holds

  // List subtraction is "commutative".
  @induct
  def subComm[T](xs: List[T], y: T, x: T): Boolean = {
    (xs - y) - x == (xs - x) - y
  }.holds

  // Trying to subtract something that isn't there in the first place does
  // nothing.
  @induct
  def subId[T](xs: List[T], x: T): Boolean = {
    require(!xs.contains(x))
    xs - x == xs
  }.holds

  // List substraction and unique "commute".
  // May need a larger timeout to verify.
  def subUniqueComm[T](xs: List[T], x: T): Boolean = {
    (xs - x).unique == xs.unique - x
  }.holds because {
    xs match {
      case Nil() => trivial
      case (y :: ys) => if (y == x) {
        xs.unique - x                ==| trivial                  |
        (y :: (ys.unique - y)) - x   ==| trivial                  |
        (ys.unique - y) - x          ==| subComm(ys.unique, y, x) |
        (ys.unique - x) - y          ==| subUniqueComm(ys, x)     |
        (ys - x).unique - y          ==| trivial                  |
        ((x :: ys) - x).unique - y   ==| trivial                  |
        (xs - x).unique - x          ==| (uniqueNotContains(xs - x, x) &&
                                            subId((xs - x).unique, x)) |
        (xs - x).unique
      }.qed else {
        (xs - x).unique              ==| trivial                  |
        ((y :: ys) - x).unique       ==| trivial                  |
        (y :: (ys - x)).unique       ==| trivial                  |
        (y :: ((ys - x).unique - y)) ==| subUniqueComm(ys, x)     |
        (y :: ((ys.unique - x) - y)) ==| subComm(ys.unique, y, x) |
        (y :: ((ys.unique - y) - x)) ==| trivial                  |
        ((y :: (ys.unique - y)) - x) ==| trivial                  |
        xs.unique - x
      }.qed
    }
  }

  // List subtraction is idempotent.
  @induct
  def subIdem[T](xs: List[T], x: T): Boolean = {
    (xs - x) == ((xs - x) - x)
  }.holds

  // This is the main result about sets. With this, we can call unique on any
  // list and call it a set.
  def uniqueIdem[T](l: List[T]): Boolean = {
    l.unique == l.unique.unique
  }.holds because {
    l match {
      case Nil() => trivial
      case (x :: xs) => {
        l.unique.unique                     ==| trivial                     |
        (x :: (xs.unique - x)).unique       ==| trivial                     |
        (x :: ((xs.unique - x).unique - x)) ==| subUniqueComm(xs.unique, x) |
        (x :: ((xs.unique.unique - x) - x)) ==| uniqueIdem(xs)              |
        (x :: ((xs.unique - x) - x))        ==| subIdem(xs.unique, x)       |
        (x :: (xs.unique - x))              ==| trivial                     |
        l.unique
      }.qed
    }
  }

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
    that forall { x => this contains x }
  }

  def ==(that: Set[T]): Boolean = {
    (this subsetOf that) && (that subsetOf this)
  }

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

