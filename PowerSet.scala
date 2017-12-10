package powerset

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._



// object PowerSet {
//   def setEq[T](a: List[T], b: List[T]): Boolean = {
//     require(isSet(a) && isSet(b))
//     a.content == b.content
//   }

//   // === Power Set

//   // Given a list, returns its powerset: the set of all "subsets" of that list.
//   // If the input list is sorted, then the returned lists will also be sorted.
//   def powerSet[T](set: List[T]): List[List[T]] = {
//     require(isSet(set))

//     set match {
//       case Nil()      => List(Nil())
//       case Cons(h, t) =>
//         val ps = powerSet(t)
//         ps ps.map { h :: _ }
//     }
//   }

//   @ignore
//   def powerSetHasSets[T](set: List[T]): Boolean = {
//     require(isSet(set))
//     powerSet(set) forall { isSet _ }
//   }.holds because {
//     set match {
//       case Nil() => trivial
//       case (x :: xs) =>
//         val ps = powerSet(xs)

//         check(ps ++ ps.map(x :: _)).forall({ isSet _}) &&
//         check(ps.forall({ isSet _}) && ps.map(x :: _).forall({ isSet _})) &&
//         powerSetHasSets(xs)
//     }
//   }

//   // Computes 2^x (two to the power of x).
//   @ignore
//   def pow2(x: BigInt): BigInt = {
//     require(x >= 0)

//     if (x == 0) BigInt(1)
//     else 2 * pow2(x - 1)
//   } ensuring { _ > 0 }

//   // Proof that the cardinality of the powerset is two to the power of the
//   // cardinality of the input set.
//   @ignore
//   def powerSetSize(l: List[BigInt]): Boolean = {
//     powerSet(l).size == pow2(l.size)
//   }.holds because {
//     l match {
//       case Nil() => trivial
//       case Cons(x, xs) => {
//         powerSet(x :: xs).size == pow2(l.size)                            ==| trivial          |
//         (powerSet(xs) ++ powerSet(xs).map(x :: _)).size == pow2(l.size)   ==| trivial          |
//         powerSet(xs).size + powerSet(xs).map(x :: _).size == pow2(l.size) ==| trivial          |
//         powerSet(xs).size + powerSet(xs).size == pow2(l.size)             ==| trivial          |
//         2 * powerSet(xs).size == pow2(l.size)                             ==| powerSetSize(xs) |
//         2 * pow2(xs.size) == pow2(l.size)
//       }.qed
//     }
//   }

//   @ignore
//   def appContains[T](a: List[T], b: List[T], x: T): Boolean = {
//     require(isSet(a) && isSet(b))
//     (a.contains(x) || b.contains(x)) == (a ++ b).contains(x)
//   }.holds

// }
