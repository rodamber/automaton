package powerset

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.math._
import stainless.proof._


sealed abstract class MyList[T] {

  def size: Int = (this match {
                     case MyNil() => 0
                     case MyCons(h, t) => 1 + t.size
                   }) ensuring { res => (this, res) passes {
                                  case MyNil() => 0
                                  case MyCons(_, MyNil()) => 1
                                  case MyCons(_, MyCons(_, MyNil())) => 2
                                }}
}
case class MyCons[T](h: T, t: MyList[T]) extends MyList[T]
case class MyNil[T]() extends MyList[T]

object PowerSet {
  // def powerSet(set: List[BigInt]): List[List[BigInt]] = {
  //   set match {
  //     case Nil()      => List(Nil())
  //     case Cons(h, t) =>
  //       val ps = powerSet(t)
  //       ps ++ ps.map { h :: _ }
  //   }
  // } //ensuring {
  //   (res: List[List[BigInt]]) => (set, res) passes {
  //     case Nil() => List(Nil())
  //     case Cons(BigInt(1), Cons(BigInt(2), Cons(BigInt(3), Nil()))) =>
  //       List(Nil(), 
  //            List(BigInt(3)), 
  //            List(BigInt(2)),
  //            List(BigInt(2), BigInt(3)),
  //            List(BigInt(1)), 
  //            List(BigInt(1), BigInt(3)),
  //            List(BigInt(1), BigInt(2)), 
  //            List(BigInt(1), BigInt(2), BigInt(3)))
  //   }
  // }

  def pow2(x: BigInt): BigInt = {
    require(x >= BigInt(0))

    if (x == BigInt(0)) BigInt(1)
    else BigInt(2) * pow2(x - BigInt(1))
  } ensuring {
    (res: BigInt) => res > BigInt(0) && (x, res).passes{
      case BigInt(0) => BigInt(1)
      case BigInt(1) => BigInt(2)
      case BigInt(2) => BigInt(4)
      case BigInt(3) => BigInt(8)
      case BigInt(4) => BigInt(16)
      case BigInt(5) => BigInt(32)
      case BigInt(6) => BigInt(64)
    }
  }


  // def powerSetSize(l: List[BigInt]): Boolean = {
  //   powerSet(l).size == pow2(l.size)
  // }.holds because {
  //   l match {
  //     case Nil() => check(l.size == 0) && check(pow2(l.size) == 1) && check(powerSet(l) == List(Nil())) && check(powerSet(l).size == 1)
  //     case _ => false
  //   }
  // }






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
