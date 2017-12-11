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
    val validStates = nfa.validStates.powerSet

    val move = { (s: Set[State], w: Sym) =>
      nfa.epsClosure(nfa.move(s, Some(w)))
    }

    val initialState = nfa.epsClosure(Set.set(nfa.initialState))
    val acceptStates = validStates filter { s =>
      (s & nfa.acceptStates).nonEmpty
    }

    DFA(validStates, move, initialState, acceptStates)
  }

  def dfaEquivNfa[State, Sym](nfa: NFA[State, Sym], states: Set[State],
                              word: List[Sym]): Boolean = {
    require(nfa.epsClosed(states))
    val dfa = DFA(nfa)

    nfa.run(states, word) == dfa.run(states, word)
  }.holds because {
    val dfa = DFA(nfa)

    word match {
      case Nil() => {
        nfa.run(states, word)  ==| trivial               |
        nfa.epsClosure(states) ==| nfa.epsClosed(states) |
        states                 ==| trivial               |
        dfa.run(states, word)
      }.qed

      case (w :: ws) => {
        dfa.run(states, word)                                  ==| trivial |
        dfa.run(dfa.move(states, w), ws)                       ==| trivial |
        dfa.run(dfa.move(states, w), ws)                      ==| trivial |
        dfa.run(nfa.epsClosure(nfa.move(states, Some(w))), ws) ==| dfaEquivNfa(nfa, nfa.epsClosure(nfa.move(states, Some(w))), ws) |
        nfa.run(nfa.epsClosure(nfa.move(states, Some(w))), ws) ==| trivial |
        nfa.run(states, word)
      }.qed
    }
  }

}

case class DFA[State, Sym](
  validStates: Set[State],
  move: (State, Sym) => State,
  initialState: State,
  acceptStates: Set[State]
) {
  require {
    validStates.nonEmpty &&
    validStates.contains(initialState) &&
    acceptStates.subsetOf(validStates) &&
    forall((s: State, w: Sym) => validStates contains move(s, w))
  }

  def run(state: State, word: List[Sym]): State = {
    word match {
      case Nil() => state
      case (w :: ws) => run(move(state, w), ws)
    }
  } ensuring { validStates contains _ }

  def accepts(word: List[Sym]): Boolean = {
    acceptStates contains run(initialState, word)
  }

}

// We represent ε-moves as by passing a None() to the transition function.
// The ε character/word is never representend explicitly.

case class NFA[State, Sym](
  validStates: Set[State],
  move: (State, Option[Sym]) => Set[State],
  initialState: State,
  acceptStates: Set[State]
) {
  require {
    validStates.nonEmpty &&
    validStates.contains(initialState) &&
    acceptStates.subsetOf(validStates) &&
    forall((s: State, ow: Option[Sym]) => move(s, ow) subsetOf validStates)
  }

  def move(states: Set[State], w: Option[Sym]): Set[State] = {
    states match {
      case (ss + s) => move(s, w) ++ move(ss, w)
      case _ => Set.empty
    }
  } ensuring { _ subsetOf validStates }

  def run(states: Set[State], word: List[Sym]): Set[State] = {
    word match {
      case Nil() => epsClosure(states)
      case (w :: ws) =>
        val newStates = move(states, Some(w))
        run(epsClosure(newStates), ws)
    }
  } ensuring { _ subsetOf validStates }

  def epsClosure(states: Set[State]): Set[State] = {
    val newStates: Set[State] = move(states, None())

    if (newStates == states) newStates
    else epsClosure(newStates)
  } ensuring {
    (epsClosed _) && (_ subsetOf validStates)
  }

  def epsClosed(states: Set[State]): Boolean = {
    states == epsClosure(states)
  }

  def accepts(word: List[Sym]): Boolean = {
    val start = epsClosure(Set.set(initialState))
    (run(start, word) & acceptStates).nonEmpty
  }

}
