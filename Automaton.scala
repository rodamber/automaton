package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.math._
import stainless.proof._

import set._


case class Automaton[State, Sym](
  validStates : Set[State],
  trans       : (State, Sym) => Set[State]
) {
  require {
    forall((s: State, w: Sym) => trans(s, w) subsetOf validStates)
  }

  def move(states: Set[State], w: Sym): Set[State]  = {
    states match {
      case (ss + s) => trans(s, w) ++ move(ss, w)
      case _ => Set.empty
    }
  }

  def run(states: Set[State], word: List[Sym]): Set[State] = {
    word match {
      case Nil() => states
      case (w :: ws) => run(move(states, w), ws)
    }
  }

  def det: Automaton[Set[State], Sym] = {
    Automaton(validStates.powerSet,
              { (s: Set[State], w: Sym) => Set.set(move(s, w)) })
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
    Set.set(run(states, word)) == det.run(Set.set(states), word)
  }.holds because {
    word match {
      case Nil() => {
        Set.set(run(states, word))     ==| trivial |
        Set.set(states)
      }.qed && {
        det.run(Set.set(states), word) ==| trivial |
        Set.set(states)
      }.qed
      case (w :: ws) => {
        det.run(Set.set(states), word)                              ==| trivial |
        det.run(Set.set(List(states)), word)                        ==| trivial |
        det.run(Set(List(states).unique), word)                     ==| Set.isSet(List(states)) |
        det.run(Set(List(states)), word)                            ==| trivial |
        det.run(det.move(Set(List(states)), w), ws)                 ==| trivial |
        det.run(det.trans(states, w) ++ det.move(Set.empty, w), ws) ==| trivial |
        det.run(det.trans(states, w) ++ Set.empty, ws)              ==| ListSpecs.rightUnitAppend(det.trans(states, w).list) |
        det.run(det.trans(states, w), ws)                           ==| trivial |
        det.run(Set.set(move(states, w)), ws)                       ==| detSound(move(states, w), ws) |
        Set.set(run(move(states, w), ws))                           ==| trivial |
        Set.set(run(states, ws))
      }.qed
    }
  }

}
