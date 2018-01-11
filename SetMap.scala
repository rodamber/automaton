package set

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._

// A class that guarantees that the underlying set is always a subset of some
// other, previously determined, set.

// Motivation: if this is used in the implementation of the automaton, maybe we
// can avoid having to prove some stuff that we currently don't know how to prove.

// Implementation idea: Maybe we could use our current implementation of Set as
// a basis for this.

case class SubSet[T](sub: List[T], super_: List[T]) {
  require(sub.content subsetOf super_.content)

  def contains(t: T): Boolean = 
    sub.contains

  def subsetOf(s: SubSet[T]): Boolean = 
    sub.content subsetOf s.sub.content

  def strictSubsetOf(s: SubSet[T]): Boolean =
    subsetOf(s) && !s.subsetOf(this)

  def eq(s: SubSet[T]): Boolean =
    subsetOf(s) && s.subsetOf(this)

  def isEmpty: Boolean =
    sub.isEmpty

  def exists(p: T => Boolean): Boolean =
    sub.exists(p)

  def size: BigInt =
    sub.unique.size

  // FIXME
  // def +(x: T): SubSet[T] = {
  //   require(super_ contains x)

  // }

}


// FIXME: The next alternative is not good, because we lose access to the
// original superset when we add or remove elements. Note that we cannot
// udpate map in-place.

// case class SubSet2[T](xs: List[T]) {

//   val map: Map[T, Boolean] = {
//     val truths: List[Boolean]   = Nil().padTo(xs.size, true)
//     val kvs: List[(T, Boolean)] = xs.zip(truths)

//     val m: Map[T, Boolean] = Map.empty

//     kvs.foldLeft(m)((acc, kv) => acc + kv)
//   }

//   def contains(t: T): Boolean = 
//     map.getOrElse(t, false)

//   def content: List[T] = 
//     xs.filter(contains _)

//   def subsetOf(s: SubSet2[T]): Boolean = 
//     content.content subsetOf s.content.content

//   def strictSubsetOf(s: SubSet2[T]): Boolean =
//     subsetOf(s) && !s.subsetOf(this)

//   def eq(s: SubSet2[T]): Boolean =
//     subsetOf(s) && s.subsetOf(this)

//   def isEmpty: Boolean =
//     content.isEmpty

//   def exists(p: T => Boolean): Boolean =
//     xs.exists((t: T) => contains(t) && p(t))

//   def size: BigInt =
//     // content.size // FIXME: Unknown call to size on SubSet2.this.content (Set[T]) with arguments List() of type List()
//     content.size

//   def +(x: T): SubSet2[T] = {
//     require(xs contains x)
//     SubSet2(x :: content)
//   }

//   def -(x: T): SubSet2[T] = {
//     require(xs contains x)
//     SubSet2(content - x)
//   }

//   def -(x: T): SubSet2[T] = {
//     require(xs contains x)
//     SubSet2(xs.filter(contains _) - x)
//   }

// }

