package set

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._


object Set {

  def isSet[T](l: List[T]): Boolean = {
    l == l.unique
  }

  @induct
  def subComm[T](xs: List[T], y: T, x: T): Boolean = {
    (xs - y) - x == (xs - x) - y
  }.holds

  def subUniqueProj[T](xs: List[T], x: T): Boolean = {
    require(!xs.contains(x))
    xs.unique - x == xs.unique
  }.holds because {
    xs match {
      case Nil() => trivial
      case (y :: ys) => {
        xs.unique - x                ==| trivial                  |
        (y :: (ys.unique - y)) - x   ==| trivial                  |
        (y :: ((ys.unique - y) - x)) ==| subComm(ys.unique, y, x) |
        (y :: ((ys.unique - x) - y)) ==| subUniqueProj(ys, x)     |
        (y :: (ys.unique - y))       ==| trivial                  |
        xs.unique
      }.qed
    }
  }

  // Needed timeout of 10 secs to verify on my machine.
  def lemma[T](xs: List[T], x: T): Boolean = {
    (xs - x).unique == xs.unique - x
  }.holds because {
    xs match {
      case Nil() => trivial
      case (y :: ys) => if (y == x) {
        xs.unique - x                ==| trivial                  |
        (y :: (ys.unique - y)) - x   ==| trivial                  |
        (ys.unique - y) - x          ==| subComm(ys.unique, y, x) |
        (ys.unique - x) - y          ==| lemma(ys, x)             |
        (ys - x).unique - y          ==| trivial                  |
        ((x :: ys) - x).unique - y   ==| trivial                  |
        (xs - x).unique - x          ==| subUniqueProj(xs - x, x) |
        (xs - x).unique
      }.qed else {
        (xs - x).unique              ==| trivial                  |
        ((y :: ys) - x).unique       ==| trivial                  |
        (y :: (ys - x)).unique       ==| trivial                  |
        (y :: ((ys - x).unique - y)) ==| lemma(ys, x)             |
        (y :: ((ys.unique - x) - y)) ==| subComm(ys.unique, y, x) |
        (y :: ((ys.unique - y) - x)) ==| trivial                  |
        ((y :: (ys.unique - y)) - x) ==| trivial                  |
        xs.unique - x
      }.qed
    }
  }


  @induct
  def subProj[T](xs: List[T], x: T): Boolean = {
    (xs - x) == ((xs - x) - x)
  }.holds

  def uniqueProj[T](l: List[T]): Boolean = {
    l.unique == l.unique.unique
  }.holds because {
    l match {
      case Nil() => trivial
      case (x :: xs) => {
        l.unique.unique                     ==| trivial               |
        (x :: (xs.unique - x)).unique       ==| trivial               |
        (x :: ((xs.unique - x).unique - x)) ==| lemma(xs.unique, x)   |
        (x :: ((xs.unique.unique - x) - x)) ==| uniqueProj(xs)        |
        (x :: ((xs.unique - x) - x))        ==| subProj(xs.unique, x) |
        (x :: (xs.unique - x))              ==| trivial               |
        l.unique
      }.qed
    }
  }

}

import Set._


case class Set[T](list: List[T]) {
  require(isSet(list))

  def contains(x: T): Boolean = {
    list contains x
  }

  def forall(p: T => Boolean): Boolean = {
    list forall p
  }

  def ++(that: Set[T]): Set[T] = {
    val app = this.list ++ that.list
    assert((app.unique == app.unique.unique) because uniqueProj(app))
    Set((this.list ++ that.list).unique)
  }

}

