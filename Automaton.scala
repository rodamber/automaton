package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.math._
import stainless.proof._


case class Automaton[State](
  S: List[State],                  // internal states
  M: (State, Char) => List[State]  // transition function
) {
  require(
    S.nonEmpty &&
      (forall((s: State, w: Char) => M(s, w).content subsetOf S.content))
  )

  // FIXME
  def validSet(s: List[State]): Boolean = {
    s.content subsetOf S.content
  }

  def move(set: List[State], w: Char): List[State] = {
    require(validSet(set))

    set match {
      case Nil()      => Nil()
      case Cons(h, t) => merge(M(h, w), move(t, w))
    }
  }

  // FIXME
  def merge(a: List[State], b: List[State]): List[State] = {
    require(validSet(a) && validSet(b))
    a ++ b
  }

  // Returns the set of possible states the NFA might be in after processing the
  // word.
  def runFrom(word: List[Char], from: List[State]): List[State] = {
    require(validSet(from))

    word match {
      case Nil()       => from
      case Cons(w, ws) => runFrom(ws, move(from, w))
    }
  }

  // FIXME
  def validSubsets(set: List[State]): List[List[State]] = {
    require(validSet(set))
    Nil()
  }

  // FIXME: adt invariant?
  def det(): Automaton[List[State]] = {
    val valid = validSubsets(S)
    val trans = { (s: List[State], w: Char) => List(move(s, w)) }

    Automaton(valid, trans)
  }

  // FIXME: Unverified.
  def detSound(word: List[Char]): Boolean = {
    val D = det()
    true

    // word match {
    //   case Nil() => (runFrom(word, from) == D.runFrom(word, List(from)).head)
    //   case Cons(x, xs) => true
        // val to1 = runFrom(List(x), from)
        // val to2 = D.runFrom(List(x), List(from))

        // (to1 == to2.head) && detSound(xs, to1)
  }.holds

}
