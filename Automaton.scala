package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.math._
import stainless.proof._

object Utils {

  // Strictly decreasing
  def strictDec(l: List[BigInt]): Boolean = {
    l match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(x, xs @ Cons(y, _)) => (x < y) && strictDec(xs)
    }
  }

  @induct
  def strictDecSorted(l: List[BigInt]): Boolean = {
    require(strictDec(l))
    ListOps.isSorted(l)
  }.holds

}
import Utils._

case class DFA(states: List[List[BigInt]], trans: (List[BigInt], Char) => List[BigInt]) {
  require(forall((s: List[BigInt], w: Char) => states contains trans(s, w)))

  // FIXME
  def runFrom(word: List[Char], from: List[BigInt]): List[BigInt] = {
    Nil()
  }
}

case class NFA(states: List[BigInt], trans: (BigInt, Char) => List[BigInt]) {
  require(forall((s: BigInt, w: Char) => trans(s, w).content subsetOf states.content))

  def validStates(s: List[BigInt]): Boolean = {
    (s.content subsetOf states.content) && strictDec(s)
  }

  def move(set: List[BigInt], w: Char): List[BigInt] = {
    require(validStates(set))

    set match {
      case Nil()      => Nil()
      case Cons(h, t) => merge(trans(h, w), move(t, w))
    }
  }

  def merge(a: List[BigInt], b: List[BigInt]): List[BigInt] = {
    require(validStates(a) && validStates(b))

    (a, b) match {
      case (Nil(), _) => b
      case (_, Nil()) => a
      case (Cons(x, xs), Cons(y, ys)) =>
        if (x < y) x :: merge(xs, b)
        else       y :: merge(a,  ys)
    }
  }

  def mergeLemma(a: List[BigInt], b: List[BigInt]): Boolean = {
    require(validStates(a) && validStates(b))

    strictDec(merge(a, b)) && {
      (a, b) match {
        case (Nil(), _) => trivial
        case (_, Nil()) => trivial
        case (Cons(x, xs), Cons(y, ys)) => mergeLemma(xs, b) || mergeLemma(a,  ys)
      }
    }
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

  // FIXME
  def validSubsets(set: List[BigInt]): List[List[BigInt]] = {
    require(validStates(set))
    Nil()
  }

  // FIXME: adt invariant?
  def det(): DFA = DFA(validSubsets(states),
                       { (s: List[BigInt], w: Char) => move(s, w) })

  // FIXME: Unverified.
  def detSound(word: List[Char], from: List[BigInt]): Boolean = {
    val dfa = det()
    runFrom(word, from) == dfa.runFrom(word, from)
  }.holds

}
