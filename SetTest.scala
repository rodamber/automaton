package set

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._


object Set {

  def empty[T]: Set[T] = Set(Nil[T]())

  def singleton[T](x: T): Set[T] = Set(List(x))

  def isSet[T](l: List[T]): Boolean = {
    l == l.unique
  }

  def tailIsSet[T](l: List[T]): Boolean = {
    require(isSet(l))

    l match {
      case Nil() => true
      case (_ :: xs) => isSet(xs)
    }
  }.holds because {
    l match {
      case Nil() => trivial
      case (x :: xs) => tailNotContains(l) && uniqueNotContains(xs, x) && {
        xs                         ==| subCons(xs, x)           |
        (x :: xs) - x              ==| isSet(x :: xs)           |
        (x :: xs).unique - x       ==| trivial                  |
        (x :: (xs.unique - x)) - x ==| trivial                  |
        (xs.unique - x) - x        ==| subUnique1(xs.unique, x) |
        xs.unique - x              ==| subUnique1(xs.unique, x) |
        xs.unique
      }.qed
    }
  }

  def tailNotContains[T](l: List[T]): Boolean = {
    require(isSet(l))

    l match {
      case Nil() => true
      case (x :: xs) => !xs.contains(x)
    }
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


  // @ignore
  // def apply[T](elems: T*): Set[T] = Set(List(elems : _*))

  @induct
  def subComm[T](xs: List[T], y: T, x: T): Boolean = {
    (xs - y) - x == (xs - x) - y
  }.holds

  @induct
  def subUnique1[T](xs: List[T], x: T): Boolean = {
    require(!xs.contains(x))
    xs - x == xs
  }.holds

  def subUnique[T](xs: List[T], x: T): Boolean = {
    require(!xs.contains(x))
    xs.unique - x == xs.unique
  }.holds because {
    xs match {
      case Nil() => trivial
      case (y :: ys) => {
        xs.unique - x                ==| trivial                  |
        (y :: (ys.unique - y)) - x   ==| trivial                  |
        (y :: ((ys.unique - y) - x)) ==| subComm(ys.unique, y, x) |
        (y :: ((ys.unique - x) - y)) ==| subUnique(ys, x)         |
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
        (xs - x).unique - x          ==| subUnique(xs - x, x) |
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
  def subIdem[T](xs: List[T], x: T): Boolean = {
    (xs - x) == ((xs - x) - x)
  }.holds

  def uniqueIdem[T](l: List[T]): Boolean = {
    l.unique == l.unique.unique
  }.holds because {
    l match {
      case Nil() => trivial
      case (x :: xs) => {
        l.unique.unique                     ==| trivial               |
        (x :: (xs.unique - x)).unique       ==| trivial               |
        (x :: ((xs.unique - x).unique - x)) ==| lemma(xs.unique, x)   |
        (x :: ((xs.unique.unique - x) - x)) ==| uniqueIdem(xs)        |
        (x :: ((xs.unique - x) - x))        ==| subIdem(xs.unique, x) |
        (x :: (xs.unique - x))              ==| trivial               |
        l.unique
      }.qed
    }
  }

}

import Set._


case class Set[T](list: List[T]) {
  require(isSet(list))

  // def contains(x: T): Boolean = {
  //   list contains x
  // }

  // def forall(p: T => Boolean): Boolean = {
  //   list forall p
  // }

  def ++(that: Set[T]): Set[T] = {
    val app = this.list ++ that.list
    assert(uniqueIdem(app))
    Set(app.unique)
  }

  def +(x: T): Set[T] = {
    this ++ Set(List(x))
  }

  // def map[U](f: T => U): Set[U] = {
  //   val out = this.list map f
  //   assert(uniqueIdem(out))
  //   Set(out.unique)
  // }

  def powerSet: List[Set[T]] = {
    this.list match {
      case Nil()     => List(empty)
      case (x :: xs) =>
        assert(tailIsSet(xs))
        val ps = Set(xs).powerSet
        ps ++ ps.map { _ + x }

    }
  }

}

// object SEmpty {
//   def unapply[T](set: Set[T]): Boolean = set.list match {
//     case Nil() => true
//     case Cons(x, xs) => false
//   }
// }

// object + {
//   def unapply[T](set: Set[T]): Option[(Set[T], T)] = set.list match {
//     case Nil() => None()
//     case Cons(x, xs) => Some((Set(xs), x))
//   }
// }

