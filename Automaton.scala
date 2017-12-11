package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.math._
import stainless.proof._

import set._


// In the current formulation, the automaton might not be finite, so there is
// no guarantees that it might ever terminate.
case class Automaton[State, Sym](
  trans: (State, Sym) => Set[State],
  eps: Sym
) {

  def move(states: Set[State], w: Sym): Set[State]  = {
    states match {
      case (ss + s) => trans(s, w) ++ move(ss, w)
      case _ => Set.empty
    }
  }

  def epsClosed(states: Set[State]): Boolean = {
    states == epsClosure(states)
  }

  def epsClosure(states: Set[State]): Set[State] = {
    val newStates = states flatMap { trans(_, eps) }

    if (newStates == states) newStates
    else epsClosure(newStates)
  }

  def run(states: Set[State], word: List[Sym]): Set[State] = {
    word match {
      case Nil() => states
      case (w :: ws) => run(move(states, w), ws)
    }
  }

  def det: Automaton[Set[State], Sym] = {
    Automaton({ (s: Set[State], w: Sym) => Set.set(epsClosure(move(s, w))) }, eps)
  }

  def detIsDeterministic(s: Set[State], w: Sym): Boolean = {
    det.trans(s, w).size == 1
  }.holds because {
    det.trans(s, w).size                             ==| trivial |
    Set.set(move(s, w)).size                         ==| trivial |
    Set.set(List(move(s, w))).size                   ==| trivial |
    Set(List(move(s, w)).unique).size                ==| trivial |
    List(move(s, w)).unique.size                     ==| trivial |
    Cons(move(s, w), Nil().unique - move(s, w)).size ==| trivial |
    Cons(move(s, w), Nil()).size                     ==| trivial |
    BigInt(1)
  }.qed

  def detSound(states: Set[State], word: List[Sym]): Boolean = {
    require(epsClosed(states))
    Set.set(run(states, word)) == det.run(Set.set(states), word - eps)
  }.holds because {
    (word, word - eps) match {
      case (_, Nil()) => { // word is composed only of ε's
        det.run(Set.set(states), Nil()) ==| trivial |
        Set.set(states)                 ==| someLemma1 && someLemma2 | // saying that word is only ε's and that that makes run output states
        Set.set(run(states, word))
      }.qed

      case ((w :: ws), (z :: zs)) => {
        det.run(Set.set(states), word - eps)               ==| trivial |
        det.run(Set(List(states).unique), word - eps)      ==| Set.isSet(List(states)) |
        det.run(Set(List(states)), word - eps)             ==| trivial |
        det.run(det.move(Set(List(states)), z), zs)        ==| trivial |
        det.run(det.trans(states, z) ++ Set.empty, zs)     ==| ListSpecs.rightUnitAppend(det.trans(states, w).list) |
        det.run(det.trans(states, z), zs)                  ==| trivial |
        det.run(Set.set(epsClosure(move(states, z))), zs)  ==| detSound(epsClosure(move(states, z)), zs) |
        Set.set(run(epsClosure(move(states, w)), ws))
      }.qed && (
        if (w == eps) {
          Set.set(run(epsClosure(move(states, w)), ws))    ==| epsClosed(states) |
          Set.set(run(states, ws))                         ==| (epsClosed(states) && (w == eps)) |
          Set.set(run(states, word))
        }.qed else {
          Set.set(run(epsClosure(move(states, w)), ws))    ==| epsClosed(states) |
            // ...
          Set.set(run(states, word))
        }.qed
      )

      case _ => trivial
    }
  }

}
