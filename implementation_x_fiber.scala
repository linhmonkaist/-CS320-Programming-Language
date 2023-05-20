package cs320

import Value._

object Implementation extends Template {
  private def intVop(
      op: (BigInt, BigInt) => BigInt
  ): (Value, Value) => Value = {
    case (IntV(a), IntV(b)) => IntV(op(a, b))
    case (a, b)             => error(s"not a number $a, $b")
  }
  private def booVop(
      op: (BigInt, BigInt) => Boolean
  ): (Value, Value) => Value = {
    case (IntV(a), IntV(b)) => BooleanV(op(a, b))
    case _                  => error("not a number for boolean")
  }
  private val intAdd = intVop(_ + _)
  private val intMul = intVop(_ * _)
  private val intDiv = intVop(_ / _)
  private val intMod = intVop(_ % _)
  private val booEq = booVop(_ == _)
  private val booLt = booVop(_ < _)
  private def mergetuple(hea: Value, tai: Value): TupleV = {
    (hea, tai) match {
      case (TupleV(headtuple), TupleV(tailtuple)) =>
        TupleV(hea :: tailtuple)
      case (IntV(he), TupleV(tailtuple))      => TupleV(hea :: tailtuple)
      case (BooleanV(he), TupleV(tailtuple))  => TupleV(hea :: tailtuple)
      case (NilV, TupleV(tailtuple))          => TupleV(NilV :: tailtuple)
      case (ConsV(l, r), TupleV(tailtuple))   => TupleV(hea :: tailtuple)
      case (CloV(l, r, b), TupleV(tailtuple)) => TupleV(hea :: tailtuple)
      case (ContV(l), TupleV(tailtuple))      => TupleV(hea :: tailtuple)
      case (_, NilV)                          => TupleV(hea :: Nil)
      case _                                  => error("line 29")
    }
  }

  def interp(expr: Expr): Value = {

    def inter(expr: Expr, env: Env, k: Cont, h: Handler): Value = expr match {
      case Id(name) =>
        k(env.getOrElse(name, error(s"don't have that name $name")))
      case IntE(n)     => k(IntV(n))
      case BooleanE(b) => k(BooleanV(b))
      case Add(l, r) =>
        inter(l, env, lv => inter(r, env, rv => k(intAdd(lv, rv)), h), h)
      case Mul(l, r) =>
        inter(l, env, lv => inter(r, env, rv => k(intMul(lv, rv)), h), h)
      case Div(l, r) =>
        inter(
          l,
          env,
          lv =>
            inter(
              r,
              env,
              rv => {
                if (rv == IntV(0)) error("can not be 0")
                else k(intDiv(lv, rv))
              },
              h
            ),
          h
        )
      case Mod(l, r) =>
        inter(
          l,
          env,
          lv =>
            inter(
              r,
              env,
              rv => {
                if (rv == IntV(0)) error("can not be 0")
                else k(intMod(lv, rv))
              },
              h
            ),
          h
        )
      case Eq(l, r) =>
        inter(l, env, lv => inter(r, env, rv => k(booEq(lv, rv)), h), h)
      case Lt(l, r) =>
        inter(l, env, lv => inter(r, env, rv => k(booLt(lv, rv)), h), h)
      case If(c, l, r) => {
        inter(c, env, interc => {
        interc match {
          case BooleanV(true)  => inter(l, env, k, h)
          case BooleanV(false) => inter(r, env, k, h)
          case a               => error(s"not a condition in if $a")
        }
        }, h)
      }
      case TupleE(li) => {
        //val v= li.foldLeft[List[Value]](Nil)((a,b) => (inter(a, env, x => x, h) :: b))
        val v = li match {
          case Nil => k(NilV)
          case headli :: tli =>
            inter(
              headli,
              env,
              interhead => {
                inter(
                  TupleE(tli),
                  env,
                  intertli => k(mergetuple(interhead, intertli)),
                  h
                )
              },
              h
            )
        }
        v
      }
      case Proj(ex, i) => {
        inter(
          ex,
          env,
          interex => {
            interex match {
              case TupleV(a) => {
                if (a.size >= i) k(a(i - 1))
                else error("out of range of tuple")
              }
              case b => error(s"not a tuple $b")
            }
          },
          h
        )
      }
      case NilE => k(NilV)
      case ConsE(head, t) => {
        inter(
          head,
          env,
          intervo => {
            inter(
              t,
              env,
              intervs => {
                intervs match {
                  case NilV        => k(ConsV(intervo, NilV))
                  case ConsV(a, b) => k(ConsV(intervo, intervs))
                  case _           => error("not a list, conse")
                }
              },
              h
            )
          },
          h
        )
      }
      case Empty(ex) => {
        inter(
          ex,
          env,
          interv => {
            interv match {
              case NilV        => k(BooleanV(true))
              case ConsV(h, t) => k(BooleanV(false))
              case _           => error("not a list in empty")
            }
          },
          h
        )
      }
      case Head(ex) => {
        inter(
          ex,
          env,
          interex => {
            interex match {
              case ConsV(h, t) => k(h)
              case _           => error("not a nonemplty list head")
            }
          },
          h
        )
      }
      case Tail(ex) => {
        inter(
          ex,
          env,
          interex => {
            interex match {
              case ConsV(h, t) => k(t)
              case _           => error("not a nonempty list tail")
            }
          },
          h
        )
      }
      case Val(name, ex, body) => {
        inter(
          ex,
          env,
          interex => {
            inter(body, env + (name -> interex), k, h)
          },
          h
        )
      }
      //new case for continuation
      case Vcc(name, body) => inter(body, env + (name -> ContV(k)), k, h)
      case Fun(args, body) => k(CloV(args, body, env))
      case RecFuns(funs, body) => {
        val x = funs.foldRight[List[String]](Nil) { (a, b) =>
          {
            a match {
              case FunDef(name, params, bo) => name :: b
            }
          }
        }
        val v = funs.foldRight[List[CloV]](Nil) { (a, b) =>
          {
            a match {
              case FunDef(name, params, bo) => CloV(params, bo, env) :: b
            }
          }
        }
        val ienv = env ++ (x zip v).toMap
        for (i <- v) {
          i match {
            case CloV(params, bo, envv) => {
              i.env = env ++ (x zip v).toMap
            }
            case _ => error("not a fic")
          }
        }
        inter(body, ienv, k, h)
      }
      case App(fun, args) => {
        inter(fun,
          env,
          v => {
            inter(
              TupleE(args),
              env,
              interargs => {
                interargs match {
                  case TupleV(listargs) => {
                    v match {
                      case CloV(paras, body, envv) => {
                        if (paras.length != listargs.length)
                          error("wrong arity")
                        else {
                          val l = (paras zip listargs).toMap
                          inter(body, envv ++ l, k, h)
                        }
                      }
                      case ContV(newk) => {
                        if (listargs.length != 1) error("line 182")
                        else newk(listargs(0))
                      }
                      case _ => error("not a function")
                    }
                  }
                  case NilV => {
                    v match {
                      case CloV(paras, body, envv) => {
                        if (paras.length != 0)
                          error("wrong arity")
                        else {
                          inter(body, envv, k, h)
                        }
                      }
                      case a => error(s"not a func $a")
                  }
                }
                  case bg => error(s"not a tuple $bg, line 260")
                }
              },
              h
            )
          },
          h
        )
      }
      case Test(ex, typ) => {
        inter(ex, env, v => {
        (con(v), typ) match {
          case (IntT, IntT)           => k(BooleanV(true))
          case (BooleanT, BooleanT)   => k(BooleanV(true))
          case (TupleT, TupleT)       => k(BooleanV(true))
          case (ListT, ListT)         => k(BooleanV(true))
          case (FunctionT, FunctionT) => k(BooleanV(true))
          case (_)                    => k(BooleanV(false))
        }
        }, h)
      }
      //new case for x-fiber
      case Throw(exc) => {
        inter(
          exc,
          env,
          v => {
            h match {
              case Handler(eh, envh, kh, hhOpt) => {
                hhOpt
                  .map { hh =>
                    inter(
                      eh,
                      envh,
                      vh => {
                        vh match {
                          case CloV(x, ec, envc) => {
                            if (x.length != 1) { error("line 159") }
                            else {
                              val nenvh = (x zip (v :: Nil)).toMap
                              inter(ec, envc ++ nenvh, kh, hh)
                            }
                          }
                          case ContV(nk) => nk(v)
                          case _         => error("line 166")
                        }
                      },
                      hh
                    )
                  }
                  .getOrElse(error("line 220"))
              }
              case _ => error("line 170")
            }
          },
          h
        )
      }
      case Try(exp, hand) => {
        val hnew = Handler(hand, env, k, Some(h))
        inter(exp, env, k, hnew)
      }
    }
    inter(expr, Map(), x => x, Handler(NilE, Map(), x => x, None))
  }

  private def con(a: Value): Type = a match {
    case IntV(x)       => IntT
    case BooleanV(x)   => BooleanT
    case TupleV(x)     => TupleT
    case NilV          => ListT
    case ConsV(h, t)   => ListT
    case CloV(f, x, e) => FunctionT
    case ContV(a)      => FunctionT
    case _             => error("not a value")
  }
}
