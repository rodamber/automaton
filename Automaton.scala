package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.math._
import stainless.proof._


object Utils {

  def powerSet[A](l: List[A]): List[List[A]] = {
    l match {
      case Nil() => List(Nil())
      case Cons(h, t) =>
        val ps = powerSet(t)
        ps ++ ps.map { h :: _ }
    }
  }


  def isSubsequenceOf[T](L: List[T], S: List[T]): Boolean = {
    (L, S) match {
      case (Nil(), _) => true
      case (_, Nil()) => false
      case (Cons(l, ls), Cons(s, ss)) => {
        if (l == s) isSubsequenceOf(ls, ss)
        else isSubsequenceOf(L, ss)
      }
    }
  }


  // Same as isSorted, but with a custom order.
  def isOrdered[T](L: List[T], leq: (T, T) => Boolean): Boolean = L match {
    case Nil()          => true
    case Cons(_, Nil()) => true
    case Cons(a, tail @ Cons(b, _)) => leq(a, b) && isOrdered(tail, leq)
  }


  def subsequenceIsOrdered[T](l: List[T], s: List[T], leq: (T, T) => Boolean): Boolean = {
    require(isOrdered(s, leq))
    isSubsequenceOf(l, s) ==> isOrdered(l, leq)
  }.holds

}

import Utils._

case class Automaton[State](
  S: List[State],                  // internal states
  M: (State, Char) => List[State], // transition function
  S0: State,                       // initial states
  F: List[State],                  // final states

  // We need some way to order the states.
  // FIXME: We'll probably have problems with this.
  leq: (State, State) => Boolean
) {
  require(S.nonEmpty && isOrdered(S, leq))

  require(forall((s: State, w: Char) => isSubsequenceOf(M(s, w), S)))

  require(S contains S0)
  require(isSubsequenceOf(F, S))


  def validSet(L: List[State]): Boolean = {
    // FIXME: The last condition should not be needed to be stated explicitly.
    isSubsequenceOf(L, S) && isOrdered(L, leq)
  }


  // flatMap
  // Removes repeated elements. Strictly ordered.
  def unionMap(set: List[State], f: State => List[State]): List[State] = {
    require(isOrdered(set, leq))
    require(forall((s: State) => isOrdered(f(s), leq)))

    set match {
      case Nil()      => Nil()
      case Cons(h, t) => merge(f(h), unionMap(t, f))
    }
  }


  // Removes repeated elements. Strictly ordered.
  def merge(a: List[State], b: List[State]): List[State] = {
    require(isOrdered(a, leq))
    require(isOrdered(b, leq))

    (a, b) match {
      case (_, Nil()) => a
      case (Nil(), _) => b
      case (Cons(x, xs), Cons(y, ys)) =>
        if (x == y)         x :: merge(xs, ys) // FIXME
        else if (leq(x, y)) x :: merge(xs, b)  // FIXME
        else                y :: merge(a, ys)
    }
  }


  def isDeterministic: Boolean =
    forall { (s: State, c: Char) =>
      (S contains s) ==> (M(s, c).size <= 1)
    }


  def isAcceptingPath(states: List[State], word: List[Char]): Boolean = {
    require(states.content subsetOf S.content)

    states match {
      case Nil() => false
      case Cons(s, _) => F.contains(s) && isPath(states, word, S0)
    }
  }


  def isPath(states: List[State], word: List[Char], from: State): Boolean = {
    require(states.content subsetOf S.content)
    require(S contains from)

    (states, word) match {
      case (Cons(s, Nil()), Nil()) =>
        from == s
      case (Cons(t, ss @ Cons(s, _)), Cons(w, ws)) =>
        M(s, w).contains(t) && isPath(ss, ws, from)
      case _ =>
        false
    }
  }


  def mkPath(word: List[Char], from: State): Option[List[State]] = {
    require(S contains from)

    word match {
      case Nil()       => Some(List(from))
      case Cons(w, ws) => mkPath(ws, from) match {
        case Some(path) => path match {
          case Cons(s, _) => M(s, w) match {
            case Cons(t, _) => Some(t :: path)
            case Nil()      => None()
          }
        }
        case None() => None()
      }
    }
  }


  def runNFA(word: List[Char], from: List[State]): List[State] = {
    require(validSet(from))

    word match {
      case Nil()       => from
      // FIXME: There is an obvious problem here: the output of M is not
      // guaranteed to be a valid set, so the precondition to unionMap is not
      // verified.
      case Cons(w, ws) => runNFA(ws, unionMap(from, { M(_, w) }))
    }
  }


  // // FIXME:
  // def mkPathIsSound(x: List[Char], p: List[State], from: State): Boolean = {
  //   require(S contains from)
  //   require(p == mkPath(x, from))

  //   require(forall { (s: State, c: Char) => M(s, c).nonEmpty })

  //   // FIXME: These are exactly the postconditions for mkPath
  //   assert(p.content subsetOf S.content)
  //   assert(p.size == x.size + 1)

  //   isPath(p, x, List(from)) because {
  //     // FIXME: Here, the match exhaustiveness should be implied by the last assertion
  //     (p, x) match {
  //       case (Cons(s0, Nil()), Nil()) =>
  //         trivial
  //       case (Cons(sk1, ss @ Cons(sk, _)), Cons(xk, xs)) => {
  //         isPath(ss, x, List(from))  ==| mkPathIsSound(xs, ss, from) |
  //         isPath(p,  x, List(from))  ==| M(sk, xk).contains(sk1)     |
  //         trivial
  //       }.qed
  //     }
  //   }
  // }.holds


  // @ignore
  // // FIXME: adt invariant ?
  // def det(): Automaton[List[State]] = {
  //   val T = powerSet(S)
  //   val N = { (t: List[State], c: Char) =>
  //     if (T.contains(t))
  //       List(t.flatMap { M(_, c) })
  //     else Nil[List[State]]()
  //   }
  //   val t0 = List(S0)
  //   val G  = for (t <- T if (t & F).nonEmpty) yield t

  //   Automaton(T, N, t0, G)
  // } ensuring { res =>
  //   res.isDeterministic
  //   //   && forall { (t: List[State], c: Char) =>
  //   //   if ((res.S contains t))
  //   //     res.M(t, c).nonEmpty
  //   //   else true
  //   // }
  // }


  // @ignore
  // def TA_in_TDA(x: List[Char], s: List[State], t: List[State]): Boolean = {
  //   require(isAcceptingPath(s, x))
  //   // require(D == det())

  //   det().isAcceptingPath(t, x)
  // }.holds


  // def sk_in_tk(x: List[Char], s: List[State]): Boolean = {
  //   require(s.content subsetOf S.content)
  //   require(isPath(s, x, S0))

  //   val D = det()
  //   val t = D.mkPath(x, D.S0.head)

  //   assert(D.mkPathIsSound(x, t, S0))

  //   // FIXME: Follows from the previous assertion
  //   assert(D.isPath(t, x, List(S0)))

  //   // Postcondition of det
  //   assert(forall { (t: List[State], c: Char) =>
  //            require(D.S contains t)

  //            D.M(t, c).nonEmpty
  //          })

  //   // FIXME: Because s and t are paths for x from S0
  //   assert(s.nonEmpty)
  //   assert(s.size == x.size + 1)
  //   assert(t.nonEmpty)
  //   assert(t.size == x.size + 1)

  //   assert(s.size == t.size) // Trivial

  //   t.head.contains(s.head) because {
  //     (s, t, x) match {
  //       case (Cons(sk1, ss @ Cons(sk, _)), Cons(tk1, Cons(tk, _)), Cons(xk, xs)) => {
  //         tk.contains(sk)                                              ==| sk_in_tk(xs, ss) |
  //         M(sk, xk).content.subsetOf(tk.flatMap({ M(_, xk) }).content) ==| trivial          |
  //         M(sk, xk).content.subsetOf(tk1.content)                      ==| trivial          |
  //         tk1.contains(sk1)
  //       }.qed
  //       case _ => trivial
  //     }
  //   }

  // }.holds

}
