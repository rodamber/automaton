package powerset

import stainless._
import stainless.collection._
import stainless.lang._
import stainless.proof._


object PowerSet {
  def powerSet(set: List[BigInt]): List[List[BigInt]] = {
    set match {
      case Nil()      => List(Nil())
      case Cons(h, t) =>
        val ps = powerSet(t)
        ps ++ ps.map { h :: _ }
    }
  }

  def pow2(x: BigInt): BigInt = {
    require(x >= 0)

    if (x == 0) BigInt(1)
    else 2 * pow2(x - 1)
  } ensuring { _ > 0 }

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

  // // FIXME: unverified
  // def powerSetPC(set: List[BigInt], subset: List[BigInt]): Boolean = {
  //   require(subset.content subsetOf set.content)
  //   powerSet(set) contains subset
  // }.holds


  // // FIXME: unverified
  // def psSorted(set: List[BigInt]): Boolean = {
  //   require(ListOps.isSorted(set))
  //   powerSet(set) forall { ListOps.isSorted _ }
  // }.holds because {
  //   set match {
  //     case Nil() => trivial
  //     case Cons(h, t) =>
  //       psSorted(t) && mapConsSorted(powerSet(t), h) && set.forall(x => h <= x)
  //   }
  // }

  // def mapConsSorted(set: List[List[BigInt]], x: BigInt): Boolean = {
  //   require(set.forall(l => ListOps.isSorted(l) && (l.nonEmpty ==> x <= l.head)))
  //   set.map(x :: _) forall { ListOps.isSorted _ }
  // }.holds because {
  //   set match {
  //     case Nil() => trivial
  //     case Cons(l, ls) => ListOps.isSorted(x :: l) && mapConsSorted(ls, x)
  //   }
  // }

  // def mapConsContent(set: List[List[BigInt]], x: BigInt): Boolean = {
  //   require(set.forall(l => ListOps.isSorted(l) && (l.nonEmpty ==> x <= l.head)))
  //   set.zip(set.map(x :: _)) forall {
  //     case (l, g) => (l.content == g.content) || (l.content == g.content + x)
  //   }
  // }.holds because {
  //   true
  // }

}
