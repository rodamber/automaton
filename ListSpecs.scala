package listspecs

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._


object ListSpecs {

  def associative[T,U](l1: List[T], l2: List[T], f: List[T] => U,
                       op: (U,U) => U): Boolean = {
   f(l1 ++ l2) == op(f(l1), f(l2))
  }

  @induct
  def forallAssoc[T](l1: List[T], l2: List[T], p: T => Boolean): Boolean = {
   associative[T, Boolean](l1, l2, _.forall(p), _ && _ )
  }.holds

  @induct
  def existsAssoc[T](l1: List[T], l2: List[T], p: T => Boolean) = {
    associative[T, Boolean](l1, l2, _.exists(p), _ || _ )
  }.holds

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

  @induct
  def subComm[T](xs: List[T], y: T, x: T): Boolean = {
    (xs - y) - x == (xs - x) - y
  }.holds

  @induct
  def subId[T](xs: List[T], x: T): Boolean = {
    require(!xs.contains(x))
    xs - x == xs
  }.holds

  @induct
  def subIdem[T](xs: List[T], x: T): Boolean = {
    (xs - x) == ((xs - x) - x)
  }.holds

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
