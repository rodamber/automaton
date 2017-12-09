package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.math._
import stainless.proof._

object Utils {

  // Strictly decreasing
  def isSortedUnique(l: List[BigInt]): Boolean = {
    l match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(x, xs @ Cons(y, _)) => (x < y) && isSortedUnique(xs)
    }
  }

  def sortedUnique(ls: List[BigInt]): List[BigInt] = {
    ls match {
      case Cons(h, t) => sortedInsert(sortedUnique(t), h)
      case Nil()      => Nil[BigInt]()
    }
  }

  def sortedInsert(ls: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSortedUnique(ls))

    ls match {
      case Nil() =>
        Cons(v, Nil())
      case Cons(h, t) =>
        if      (v == h) ls
        else if (v <  h) Cons(v, ls)
        else             Cons(h, sortedInsert(t, v))
    }
  }

  def merge(a: List[BigInt], b: List[BigInt]): List[BigInt] = {
    require(isSortedUnique(a) && isSortedUnique(b))

    (a, b) match {
      case (Nil(), _) => b
      case (_, Nil()) => a
      case (Cons(x, xs), Cons(y, ys)) =>
        if      (x == y) x :: merge(xs, ys)
        else if (x <  y) x :: merge(xs, b)
        else             y :: merge(a,  ys)
    }
  } ensuring {
    res => isSortedUnique(res) && res.content == a.content ++ b.content
  }

  // def sortedUniqueProp(set: List[List[BigInt]], x: BigInt): Boolean = {
  //   require(set forall { l => isSortedUnique(l) && (l.nonEmpty ==> x < l.head) })
  //   set.map(x :: _) forall { isSortedUnique _ }
  // }.holds because {
  //   set.map(x :: _) forall { l =>
  //     l match {
  //       case Cons(y, ys) => (x == y) && isSortedUnique(ys)
  //     }
  //   }
  // }

  // @induct
  // def mapProp(l: List[List[BigInt]], x: BigInt): Boolean = {
  //   l.map(x :: _) forall(_.head == x)
  // }.holds

  def sortedUniquePC(ls: List[BigInt]): Boolean = {
    isSortedUnique(sortedUnique(ls))
  }.holds because {
    ls match {
      case Nil() => trivial
      case Cons(x, xs) => sortedUniquePC(xs) && sortedInsertPC(sortedUnique(xs), x)
    }
  }

  @induct
  def sortedInsertPC(ls: List[BigInt], v: BigInt): Boolean = {
    require(isSortedUnique(ls))

    val x = sortedInsert(ls, v)
    isSortedUnique(x) && ((x.content == ls.content + v) || x.content == ls.content)
  }.holds

}
import Utils._

case class DFA(states: List[List[BigInt]], trans: (List[BigInt], Char) => List[BigInt]) {
  require(forall((s: List[BigInt], w: Char) => states contains trans(s, w)))

  def validState(s: List[BigInt]): Boolean = (states contains s)

  def runFrom(word: List[Char], from: List[BigInt]): List[BigInt] = {
    require(validState(from))

    word match {
      case Nil() => from
      case Cons(w, ws) => runFrom(ws, trans(from, w))
    }
  }

  def runFromPC(word: List[Char], from: List[BigInt]): Boolean = {
    require(validState(from))
    validState(runFrom(word, from))
  }.holds because {
    word match {
      case Nil() => trivial
      case Cons(w, ws) =>
        val to = trans(from, w)
        (states contains to) && runFromPC(ws, to)
    }
  }
}

case class NFA(states: List[BigInt], trans: (BigInt, Char) => List[BigInt]) {
  require(
    isSortedUnique(states) &&
    forall((s: BigInt, w: Char) => trans(s, w).content subsetOf states.content))

  def validStates(s: List[BigInt]): Boolean = {
    (s.content subsetOf states.content) && isSortedUnique(s)
  }

  def move(set: List[BigInt], w: Char): List[BigInt] = {
    require(validStates(set))

    set match {
      case Nil()      => Nil()
      case Cons(h, t) => merge(trans(h, w), move(t, w))
    }
  }

  @induct
  def movePC(set: List[BigInt], w: Char): Boolean = {
    require(validStates(set))
    validStates(move(set, w))
  }.holds

  // Returns the set of possible states the NFA might be in after processing the
  // word.
  def runFrom(word: List[Char], from: List[BigInt]): List[BigInt] = {
    require(validStates(from))

    word match {
      case Nil()       => from
      case Cons(w, ws) => runFrom(ws, move(from, w))
    }
  }

  def runFromPC(word: List[Char], from: List[BigInt]): Boolean = {
    require(validStates(from))
    validStates(runFrom(word, from))
  }.holds because {
    word match {
      case Nil() => trivial
      case Cons(w, ws) => movePC(from, w) && runFromPC(ws, move(from, w))
    }
  }

  // FIXME
  def validSubsets(set: List[BigInt]): List[List[BigInt]] = {
    require(validStates(set))

    set match {
      case Nil()      => List(Nil())
      case Cons(h, t) =>
        val ps = validSubsets(t)
        ps ++ ps.map { h :: _ }
    }
  } // ensuring { res => res.forall { validStates _ } }

  // FIXME
  def validSubsetsPC(set: List[BigInt]): Boolean = {
    require(validStates(set))
    validSubsets(set).forall { validStates _ }
  }.holds

  // FIXME: adt invariant?
  def det(): DFA = DFA(validSubsets(states),
                       { (s: List[BigInt], w: Char) => move(s, w) })

  def detValidStates(word: List[Char], from: List[BigInt]): Boolean = {
    require(validStates(from))

    validStates(det().runFrom(word, from))
  }.holds

  // FIXME: Unverified.
  def detSound(word: List[Char], from: List[BigInt]): Boolean = {
    val dfa = det()
    runFrom(word, from) == dfa.runFrom(word, from)
  }.holds

}
