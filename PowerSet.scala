package powerset

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._


object PowerSet {
  import ListOps._

  // Given a list, returns its powerset: the set of all "subsets" of that list.
  // If the input list is sorted, then the returned lists will also be sorted.
  def powerSet(set: List[BigInt]): List[List[BigInt]] = {
    set match {
      case Nil()      => List(Nil())
      case Cons(h, t) =>
        val ps = powerSet(t)
        ps ++ ps.map { h :: _ }
    }
  }

  // Computes 2^x (two to the power of x).
  @ignore
  def pow2(x: BigInt): BigInt = {
    require(x >= 0)

    if (x == 0) BigInt(1)
    else 2 * pow2(x - 1)
  } ensuring { _ > 0 }

  // Proof that the cardinality of the powerset is two to the power of the
  // cardinality of the input set.
  @ignore
  def powerSetSize(l: List[BigInt]): Boolean = {
    powerSet(l).size == pow2(l.size)
  }.holds because {
    l match {
      case Nil() => trivial
      case Cons(x, xs) => {
        powerSet(x :: xs).size == pow2(l.size)                            ==| trivial          |
        (powerSet(xs) ++ powerSet(xs).map(x :: _)).size == pow2(l.size)   ==| trivial          |
        powerSet(xs).size + powerSet(xs).map(x :: _).size == pow2(l.size) ==| trivial          |
        powerSet(xs).size + powerSet(xs).size == pow2(l.size)             ==| trivial          |
        2 * powerSet(xs).size == pow2(l.size)                             ==| powerSetSize(xs) |
        2 * pow2(xs.size) == pow2(l.size)
      }.qed
    }
  }

  // Defines what it means for a list to be a set.
  def isSet(l: List[BigInt]): Boolean = {
    (l match {
       case Nil() => true
       case Cons(x, xs) => !xs.contains(x) && isSet(xs)
    }) && isSorted(l)
  }
  // ensuring {
  //   res => res ==> (l.size == l.content.size)
  // }

  @induct
  def appForall[T](a: List[T], b: List[T], p: T => Boolean): Boolean = {
    (a.forall(p) && b.forall(p)) == (a ++ b).forall(p)
  }.holds

  def mapSorted(set: List[List[BigInt]], x: BigInt): Boolean = {
    require(set forall { l => isSorted(l) && (l.nonEmpty ==> x < l.head) })
    set.map(x :: _) forall { isSorted _ }
  }.holds because {
    set match {
      case Nil() => trivial
      case Cons(l, ls) => {
        (isSorted(x :: l) && ls.map(x :: _).forall(isSorted _)) ==| mapSorted(ls, x) |
        isSorted(x :: l)
      }.qed
    }
  }

  def powerSetSorted(set: List[BigInt]): Boolean = {
    require(isSorted(set))
    powerSet(set) forall { isSorted _ }
  }.holds because {
    set match {
      case Nil() => trivial
      case Cons(x, xs) => {
        (powerSet(xs) ++ powerSet(xs).map(x :: _)).forall(isSorted _)                    ==| appForall(powerSet(xs), powerSet(xs).map(x :: _), { isSorted _ }) |
        (powerSet(xs).forall(isSorted _) && powerSet(xs).map(x :: _).forall(isSorted _)) ==| powerSetSorted(xs)                                                |
        powerSet(xs).map(x :: _).forall(isSorted _)                                      ==| mapSorted(powerSet(xs), x)                                        |
        powerSet(xs).forall(isSorted _)
      }.qed
    }
  }


  def consSet(l: List[BigInt], x: BigInt): Boolean = {
    require(isSet(l) && (l.nonEmpty ==> x < l.head))
    isSet(x :: l)
  }.holds because {
    l match {
      case Nil() => trivial
      case Cons(y, ys) => !l.contains(x).because((x != y) && consSet(ys, x)) &&
          isSorted(x :: l)
    }
  }

  def mapConsSet(set: List[List[BigInt]], x: BigInt): Boolean = {
    require(set.forall(l => isSet(l) && (l.nonEmpty ==> x < l.head)))
    set.map(x :: _) forall { isSet _ }
  }.holds because {
    set match {
      case Nil() => trivial
      case Cons(l, ls) => consSet(l, x) && mapConsSet(ls, x)
    }
  }

  @ignore
  def powerSetSets(set: List[BigInt]): Boolean = {
    require(isSet(set))
    powerSet(set) forall { isSet _ }
  }.holds because {
    set match {
      case Nil() => trivial
      case Cons(x, xs) => {
        (powerSet(xs) ++ powerSet(xs).map(x :: _)).forall(isSet _)                 ==| appForall(powerSet(xs), powerSet(xs).map(x :: _), { isSet _ }) |
        (powerSet(xs).forall(isSet _) && powerSet(xs).map(x :: _).forall(isSet _)) ==| (powerSetSets(xs) && mapConsSet(powerSet(xs), x))              |
        // (powerSet(xs).forall(isSet _) && powerSet(xs).forall(isSet _))             ==|                                               |
        true
      }.qed
    }
  }

  // FIXME: unverified
  @ignore
  def powerSetPC(set: List[BigInt], subset: List[BigInt]): Boolean = {
    require(isSet(set) && isSet(subset) && (subset.content subsetOf set.content))
    powerSet(set) contains subset
  }.holds

}
