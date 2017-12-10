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

  def size: BigInt = list.size

  def subsetOf(that: Set[T]): Boolean =
    that.list.content subsetOf this.list.content

  def contains(x: T): Boolean = list.contains(x)

  def powerSet: List[Set[T]] = {
    this.list match {
      case Nil()     => List(empty)
      case (x :: xs) =>
        val ps = set(xs).powerSet
        ps ++ ps.map { _ + x }
    }
  }

  // def lemma: Boolean = {
  //   list match {
  //     case Nil() => true
  //     case (x :: xs) => Set(xs).powerSet forall { !_.contains(x) }
  //   }
  // }.holds

  @induct
  def appContains[T](a: List[T], b: List[T], x: T): Boolean = {
    (a.contains(x) || b.contains(x)) == (a ++ b).contains(x)
  }.holds

  // FIXME
  // We should really streamline the set interface before trying to tackle this proof.
  // It's really awkward to do all of this wrapping/unwrapping and it only makes
  // things more confusing

  @ignore
  def powerSetSound(that: Set[T]): Boolean = {
    require(that subsetOf this)
    powerSet contains that
  }.holds because {
    (this.list, that.list) match {
      case (Nil(), _) => trivial
      case (_, Nil()) => trivial
      case (x :: xs, y :: ys) =>
        val ps = set(xs).powerSet

        if (x == y) {
          powerSet.contains(that)                             ==| trivial |
          (ps ++ ps.map(_ + x)).contains(that)                ==| trivial |
          (ps.contains(that) || ps.map(_ + x).contains(that)) ==| trivial |
          ps.map(_ + x).contains(that)                        ==| trivial |
          ps.contains(set(ys))                                ==| set(xs).powerSetSound(set(ys)) |
          true
        }.qed else {
          powerSet.contains(that)                             ==| trivial |
          (ps ++ ps.map(_ + x)).contains(that)                ==| trivial |
          (ps.contains(that) || ps.map(_ + x).contains(that)) ==| trivial |
          ps.contains(that)                                   ==| set(xs).powerSetSound(that) |
          true
        }.qed
    }
  }


  // Computes 2^x (two to the power of x).
  def pow2(x: BigInt): BigInt = {
    require(x >= 0)

    if (x == 0) BigInt(1)
    else 2 * pow2(x - 1)
  } ensuring { _ > 0 }

  // Proof that the cardinality of the powerset is two to the power of the
  // cardinality of the input set.
  @ignore
  def powerSetSize: Boolean = {
    powerSet.size == pow2(size)
  }.holds because {
    list match {
      case Nil() => trivial
      case Cons(x, xs) => {
        powerSet.size                                            ==| trivial              |
        (set(xs).powerSet ++ set(xs).powerSet.map(_ + x)).size   ==| trivial              |
        set(xs).powerSet.size + set(xs).powerSet.map(_ + x).size ==| trivial              |
        set(xs).powerSet.size + set(xs).powerSet.size            ==| trivial              |
        2 * set(xs).powerSet.size                                ==| set(xs).powerSetSize |
        2 * pow2(xs.size)                                        ==| trivial              |
        pow2(list.size)                                          ==| trivial              |
        pow2(size)
      }.qed
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


