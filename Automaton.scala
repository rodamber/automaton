// In the current formulation, the automaton might not be finite.

package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.math._
import stainless.proof._

import set._

object DFA {
  def apply[State, Sym](nfa: NFA[State, Sym]): DFA[Set[State], Sym] = {
    DFA({ (s: Set[State], w: Sym) => nfa.epsClosure(nfa.move(s, w)) })
  }
}

case class DFA[State, Sym](trans: (State, Sym) => State) {
  def move(state: State, w: Sym): State = trans(state, w)

  def run(state: State, word: List[Sym]): State = {
    word match {
      case Nil() => state
      case (w :: ws) => run(move(state, w), ws)
    }
  }
}

case class NFA[State, Sym](trans: (State, Sym) => Set[State]) {
  def move(states: Set[State], w: Sym): Set[State] = {
    states match {
      case (ss + s) => trans(s, w) ++ move(ss, w)
      case _ => Set.empty
    }
  }

  def run(states: Set[State], word: List[Sym]): Set[State] = {
    word match {
      case Nil() => states
      case (w :: ws) => run(move(states, w), ws) // We should apply ε-closure here.
    }
  }

  def epsClosure(states: Set[State]): Set[State] = {
    ???
  }

  def detSound(states: Set[State], word: List[Sym]): Boolean = {
    run(states, word) == det.run(Set.set(states), word)
  }.holds
}
