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

}

import Utils._




case class Automaton[State](
  E: List[Char],                   // alphabet
  S: List[State],                  // internal states
  M: (State, Char) => List[State], // transition function
  S0: List[State],                 // initial states
  F: List[State]                   // final states
) {
  require(E.nonEmpty)
  require(S.nonEmpty)

  require(forall((s: State, c: Char) =>
            M(s,c).content subsetOf S.content))


  // require(forall((s: State, c: Char) =>
  //           !(S.contains(s) && E.contains(c)) ==> (M(s,c) == Nil[State]())))

  require(S0.content subsetOf S.content)
  require(F.content subsetOf S.content)


  def validSet(L: List[State]): Boolean = {
    validSetAux(S, L)
  }

  def validSetAux(S: List[State], L: List[State]): Boolean = {
    (S, L) match {
      case (_, Nil()) => true
      case (Nil(), _) => false
      case (Cons(s, ss), Cons(l, ls)) => {
        if (s == l) validSetAux(ss, ls)
        else validSetAux(ss, L)
      }
    }
  }


  def isDeterministic: Boolean =
    S0.size == 1 && forall { (s: State, c: Char) =>
      ((S contains s) && (E contains c)) ==> (M(s, c).size <= 1)
    }


  def isAcceptingPath(p: List[State], x: List[Char]): Boolean = {
    require(p.content subsetOf S.content)
    require(x.content subsetOf E.content)

    p match {
      case Nil() => false
      case Cons(sn, _) => F.contains(sn) && isPath(p, x, S0)
    }
  } ensuring { res =>
    res ==> (p.size == x.size + 1)
  }


  def isPath(p: List[State], x: List[Char], from: List[State]): Boolean = {
    require(p.content subsetOf S.content)
    require(x.content subsetOf E.content)
    require(from.content subsetOf S.content)

    (p, x) match {
      case (Cons(s0, Nil()), Nil()) =>
        from.contains(s0)
      case (Cons(sk1, ss @ Cons(sk, _)), Cons(xk, xs)) =>
        M(sk, xk).contains(sk1) && isPath(ss, xs, from)
      case _ =>
        false
    }
  } ensuring { res =>
    res ==> (p.size == x.size + 1)
  }


  def mkPath(x: List[Char], from: State): List[State] = {
    require(x.content subsetOf E.content)
    require(S contains from)
    // require(forall { (s: State, c: Char) => M(s, c).nonEmpty })

    x match {
      case Nil() =>
        List(from)
      case Cons(xk, xs) =>
        mkPath(xs, from) match {
          case p @ Cons(s, _) => {
            // FIXME: Why can't it verify this?
            // assert(M(s, xk).nonEmpty)

            // FIXME: Why can it verify this but can't verify the postcondition?
            // assert(M(s, xk).content subsetOf S.content)

            M(s, xk) match {
              case Cons(t, _) => t :: p
            }
          }
        }
    }
  } ensuring { res =>
    check(res.size == x.size + 1) && check(res.content subsetOf S.content)
  }

  def runNFA(x: List[Char], from: List[State]): List[State] = {
    require(x.content subsetOf E.content)
    require(validSet(from))

    x match {
      case Nil() =>
        from
      case Cons(xk, xs) =>
        from.flatMap( { M(_, c) }).content

        for (s <- from; q <- M(s, c)) yield q


    }
  }


  // // FIXME:
  // def mkPathIsSound(x: List[Char], p: List[State], from: State): Boolean = {
  //   require(x.content subsetOf E.content)
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


  @ignore
  // FIXME: adt invariant ?
  def det(): Automaton[List[State]] = {
    val T = powerSet(S)
    val N = { (t: List[State], c: Char) =>
      if (T.contains(t) && E.contains(c))
        List(t.flatMap { M(_, c) })
      else Nil[List[State]]()
    }
    val t0 = List(S0)
    val G  = for (t <- T if (t & F).nonEmpty) yield t

    Automaton(E, T, N, t0, G)
  } ensuring { res =>
    res.isDeterministic
    //   && forall { (t: List[State], c: Char) =>
    //   if ((res.S contains t) && (res.E contains c))
    //     res.M(t, c).nonEmpty
    //   else true
    // }
  }


  @ignore
  def TA_in_TDA(x: List[Char], s: List[State], t: List[State]): Boolean = {
    require(isAcceptingPath(s, x))
    // require(D == det())

    det().isAcceptingPath(t, x)
  }.holds


  // def sk_in_tk(x: List[Char], s: List[State]): Boolean = {
  //   require(s.content subsetOf S.content)
  //   require(x.content subsetOf E.content)
  //   require(isPath(s, x, S0))

  //   val D = det()
  //   val t = D.mkPath(x, D.S0.head)

  //   assert(D.mkPathIsSound(x, t, S0))

  //   // FIXME: Follows from the previous assertion
  //   assert(D.isPath(t, x, List(S0)))

  //   // Postcondition of det
  //   assert(forall { (t: List[State], c: Char) =>
  //            require(D.S contains t)
  //            require(D.E contains c)

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
