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
  def subId[T](xs: List[T], x: T): Boolean = {
    require(!xs.contains(x))
    xs - x == xs
  }.holds

  // Needed timeout of 10 secs to verify on my machine.
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

  def ++(that: Set[T]): Set[T] = {
    val app = this.list ++ that.list
    assert(uniqueIdem(app))
    Set(app.unique)
  }

  def +(x: T): Set[T] = {
    this ++ Set(List(x))
  }

  def size: BigInt = list.size

  def subsetOf(that: Set[T]): Boolean = 
    that.list.content subsetOf this.list.content

  def powerSet: List[Set[T]] = {
    this.list match {
      case Nil()     => List(empty)
      case (x :: xs) =>
        assert(tailIsSet(list))
        val ps = Set(xs).powerSet
        ps ++ ps.map { _ + x }
    }
  }

  def -(x: T): Set[T] = {
    list match {
      case Nil() => this
      case (y :: ys) =>
        if (x == y) Set(ys)
        else        Set(ys) - x
    }
  }

  def powerSetSound(that: Set[T]): Boolean = {
    require(that subsetOf this)
    powerSet contains that
  }.holds because {
    assert(tailIsSet(this.list))

    (this.list, that.list) match {
      case (_, Nil()) => trivial
      case (x :: xs, y :: ys) => 
        val ps = Set(xs).powerSet

        if (x == y) {
          powerSet.contains(that)                             ==| trivial |
          (ps ++ ps.map(_ + x)).contains(that)                ==| trivial |
          (ps.contains(that) || ps.map(_ + x).contains(that)) ==| trivial |
          (ps.contains(that) || ps.contains(that - x))        ==| trivial |
          ps.contains(that - x)                               ==| trivial |
          // ...
        }.qed else {
          powerSet.contains(that)                             ==| trivial |
          (ps ++ ps.map(_ + x)).contains(that)                ==| trivial |
          (ps.contains(that) || ps.map(_ + x).contains(that)) ==| trivial |
          ps.contains(that)                                   ==| trivial |
          // ...

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
  def powerSetSize: Boolean = {
    powerSet.size == pow2(size)
  }.holds because {
    assert(tailIsSet(list))

    list match {
      case Nil() => trivial
      case Cons(x, xs) => {
        powerSet.size                                            ==| trivial              |
        (Set(xs).powerSet ++ Set(xs).powerSet.map(_ + x)).size   ==| trivial              |
        Set(xs).powerSet.size + Set(xs).powerSet.map(_ + x).size ==| trivial              |
        Set(xs).powerSet.size + Set(xs).powerSet.size            ==| trivial              |
        2 * Set(xs).powerSet.size                                ==| Set(xs).powerSetSize |
        2 * pow2(xs.size)                                        ==| trivial              |
        pow2(list.size)                                          ==| trivial              |
        pow2(size)
      }.qed
    }
  }



}
