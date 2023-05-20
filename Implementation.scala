package cs320

object Implementation extends Template {

  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)

  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)

  object T {
    import Typed._
    case class TypeEnv(
      vars: Map[String, List[Type]]= Map(),
      tbinds: Map[String, Map[String, Type]]= Map()
    ){
      def addVar(x: String, t:List[Type]): TypeEnv= copy(vars= vars + (x -> t))
      def addTbind(x: String, cs: Map[String,Type]): TypeEnv = copy(tbinds= tbinds + (x -> cs))
    }
    def mustSame(l: Type, r:Type): Type= {
      if (isSame(l,r)) l else error(s"$l not same $r")
    }
    def isSame(l: Type, r:Type): Boolean= {
      (l,r) match {
        case (IntT, IntT) => true
        case (BooleanT,BooleanT) => true
        case (UnitT, UnitT) => true
        case (ArrowT(pt1,rt1),ArrowT(pt2, rt2)) => {
          (pt1 zip pt2).toMap.foreach{
            keyVal => if (! isSame(keyVal._1, keyVal._2)) error(s"$keyVal not same")
          }
          isSame(rt1, rt2)
        }
        case (AppT(_, targs1),AppT(_, targs2)) => {
          (targs1 zip targs2).toMap.foreach{
            keyVal => if (! isSame(keyVal._1, keyVal._2)) error(s"$keyVal not same")
          }
          true
        }
        case (VarT(name1), VarT(name2)) => {
          true
        }
        case _ => error()
      }
    }
    def unify(t1: Type, t2: Type): Unit = (resolve(t1), resolve(t2)) match {
      case (t1@VarT(_), t2) => 
        if (t1 eq t2) () 
        else if (occurs(t2,t1)) error(s"cyclic type: $t1")
        else t1.
    }
    def typeCheck(expr: Expr): Type = {
      def typeMatch(expr: Expr, tyEnv: TypeEnv): Type= {
        expr match {
          case IntE(_) => IntT 
          case Id(name, targs) => {
            /**if (!(wellForm(targs, tyEnv))) error("not a well form")
            val newtbind= tyEnv.vars.getOrElse(name, error("not have that name"))*/
            UnitT
          }
          case BooleanE(_) => BooleanT
          case UnitE => UnitT
          case Add(l,r) => {
            mustSame(typeMatch(l,tyEnv), IntT)
            mustSame(typeMatch(r,tyEnv), IntT)
          }
          case Mul(l,r) => {
            mustSame(typeMatch(l,tyEnv), IntT)
            mustSame(typeMatch(r,tyEnv), IntT)
          }
          case Div(l,r) => {
            mustSame(typeMatch(l,tyEnv), IntT)
            mustSame(typeMatch(r,tyEnv), IntT)
          }
          case Mod(l,r) => {
            mustSame(typeMatch(l,tyEnv), IntT)
            mustSame(typeMatch(r,tyEnv), IntT)
          }
          case Eq(l,r) => {
            mustSame(typeMatch(l,tyEnv), IntT)
            mustSame(typeMatch(r,tyEnv), IntT)
            BooleanT
          }
          case Lt(l,r) => {
            mustSame(typeMatch(l,tyEnv), IntT)
            mustSame(typeMatch(r,tyEnv), IntT)
            BooleanT
          }
          case Sequence(l,r) => {
            typeMatch(l, tyEnv)
            typeMatch(r, tyEnv)
          }
          case If(con,t,f) => {
            mustSame(typeMatch(con, tyEnv), BooleanT)
            mustSame(typeMatch(t, tyEnv), typeMatch(f, tyEnv))
          }
          case _ => UnitT
        }
      }
      typeMatch(expr, TypeEnv(Map(),Map()))
    }
  }

  object U {
    import Untyped._
    type Store= Map[Addr, Value]
    def interp(expr: Expr): Value = {
      def malloc(a: Store): Addr= {
        maxAddress(a) +1
      }
      def maxAddress(a: Store): Addr= {
        a.keySet.+(0).max
      }
      def intVop(op : (BigInt, BigInt) => BigInt): (Value,Value) => Value = {
        case (IntV(a), IntV(b)) => IntV(op(a, b))
        case _ => error("not a number")
      }
      def booVop(op : (BigInt, BigInt) => Boolean): (Value,Value) => Value = {
        case (IntV(a), IntV(b)) => BooleanV(op(a, b))
        case _ => error("not a number")
      }
      val intAdd = intVop(_ + _)
      val intMul = intVop(_ * _)
      val intDiv = intVop(_ / _)
      val intMod = intVop(_ % _)
      val booEq = booVop(_ == _)
      val booLt = booVop(_ < _)

      
      def inter(expr: Expr, env: Env, sto: Store): (Value, Store)= {
        expr match {
          case Id(x) => {
            val add= env.getOrElse(x, error(s"not in env $x"))
            val envValue= sto.getOrElse(add, error(s"not in sto $add"))
            envValue match {
              case ExprV(vexpr, venv) => {
                val (vmelt, mmelt)= inter(vexpr,venv,sto)
                (vmelt, mmelt + (add -> vmelt))
              }
              case _ => (envValue, sto)
            }
          }
          case IntE(n) => (IntV(n), sto)
          case BooleanE(b) => (BooleanV(b), sto)
          case UnitE => (UnitV, sto)
          case Add(l,r) => {
            val (lval, lsto)= inter(l, env, sto)
            val (rval, rsto)= inter(r, env, lsto)
            (intAdd(lval, rval), rsto)
          }
          case Mul(l,r) => {
            val (lval, lsto)= inter(l, env, sto)
            val (rval, rsto)= inter(r, env, lsto)
            (intMul(lval, rval), rsto)
          }
          case Div(l,r) => {
            val (lval, lsto)= inter(l, env, sto)
            val (rval, rsto)= inter(r, env, lsto)
            (if (rval== IntV(0)) error(s"divide 0 $lval") else intDiv(lval, rval), rsto)
          }
          case Mod(l,r) => {
            val (lval, lsto)= inter(l, env, sto)
            val (rval, rsto)= inter(r, env, lsto)
            (if (rval== IntV(0)) error(s"divide 0 $lval") else intMod(lval, rval), rsto)
          }
          case Eq(l,r) => {
            val (lval, lsto)= inter(l, env, sto)
            val (rval, rsto)= inter(r, env, lsto)
            (booEq(lval, rval), rsto)
          }
          case Lt(l,r) => {
            val (lval, lsto)= inter(l, env, sto)
            val (rval, rsto)= inter(r, env, lsto)
            (booLt(lval, rval), rsto)
          }
          case Sequence(l,r) => {
            val (lval, lsto)= inter(l,env,sto)
            inter(r, env, lsto)
          }
          case If(c,l,r) => {
            val (cval, csto) = inter(c, env, sto)
            cval match {
              case BooleanV(true) => inter(l,env, csto)
              case BooleanV(false) => inter(r,env, csto)
              case a => error(s"not a condition $a")
            }
          }
          case Val(name, exp, body) => {
            val (nval, nsto) = inter(exp, env, sto)
            val newAdd= malloc(nsto)
            inter(body, env + (name -> newAdd), nsto + (newAdd -> nval))
          }
          case RecBinds(defs, body) => {
            val (envDef, stoDef)= mergeRecBin(defs, env, sto)
            inter(body, envDef, stoDef)
          }
          case Fun(params, body) => (CloV(params, body, env), sto)
          case Assign(name, exp) => {
            val nameAddr= env.getOrElse(name, error(s"not in env $name"))
            val (expVal, expSto)= inter(exp, env, sto)
            (UnitV, expSto + (nameAddr -> expVal))
          }
          case App(fun, args) => {
            val (funVal, funsto)= inter(fun, env, sto)
            val (argslist, argSto)= foldListSto(args, env, funsto)
            funVal match {
              case CloV(param, body, funEnv) => {
                if (param.length != argslist.length) error("wrong arity")
                val hold= (param zip argslist).toMap
                val (newEnv, newSto)= listToMap(param, hold, funEnv, argSto)
                inter(body, newEnv, newSto)
              }
              case ConstructorV(name) => (VariantV(name, argslist), argSto)
              
              case a => error(s"error $a")
            }
          }
          case Match(ex, cases) => {
            val (exval, exSto)= inter(ex, env, sto)
            exval match {
              case VariantV(name, argslist) => {
                val hold= cases.filter{x => x.variant == name}
                if (hold.length == 0) error("can not find a match name")
                if (hold(0).names.length != argslist.length) error("not the same length")
                val holdmap= (hold(0).names zip argslist).toMap
                val (newEnv, newSto)= listToMap(hold(0).names, holdmap, env, exSto)
                inter(hold(0).body, newEnv, newSto)
              }
              case wild => error(s"not a varian $wild")
            }
          }
        }
      }
      def recDef(recdefi: RecDef, env: Env, sto: Store): (Env,Store)= recdefi match {
        case Lazy(name, expr) => {
          val newAdd= malloc(sto)
          (Map(name -> newAdd), sto + (newAdd -> ExprV(expr, env + (name -> newAdd))))
        }
        case RecFun(name, params, body) => {
          val newAdd= malloc(sto)
          (Map(name -> newAdd), sto + (newAdd -> CloV(params, body, env + (name -> newAdd))))
        }
        case TypeDef(variants) => {
          def mergeEnvSto(vari: List[Variant], funEnv: Env, funSto: Store): (Env, Store) = vari match {
            case Nil => (funEnv, funSto)
            case h::t => {
              val newAdd= malloc(funSto)
              if (h.empty) {
                mergeEnvSto(t, funEnv + (h.name -> newAdd), funSto + (newAdd -> VariantV(h.name, List[Value]())))
              } else {
                mergeEnvSto(t, funEnv+ (h.name -> newAdd), funSto + (newAdd -> ConstructorV(h.name)))
              }
            }
          }
          val (newEnv, newSto)= mergeEnvSto(variants, Map(), sto)
          (env ++ newEnv, newSto)
        }
      }
      def mergeRecBin(re: List[RecDef], env: Env, m: Store): (Env, Store)= re match{
        case Nil => (env, m)
        case h::t => {
          val (newEnv, newm)= recDef(h, env, m)
          mergeRecBin(t, env ++ newEnv, newm)
        }
      }
      def foldListSto(li: List[Expr], env: Env, sto: Store): (List[Value],Store)= li match {
        case Nil => (Nil,sto)
        case h:: t => {
          val (hval, hsto)= inter(h, env, sto)
          val (tval, tsto)= foldListSto(t, env, hsto)
          (hval :: tval, tsto)
        }
      }
      def listToMap(a : List[String], hold: Map[String,Value], env: Env, sto: Store): (Env,Store)= a match {
        case Nil => (env, sto)
        case h :: t => {
          val argVal= hold.getOrElse(h,error())
          val newAdd= malloc(sto)
          listToMap(t, hold, env + (h -> newAdd), sto + (newAdd -> argVal))
        }
      }
      
    /**
    def intVop(op : (BigInt, BigInt) => BigInt): (Value,Value) => Value = {
      case (IntV(a), IntV(b)) => IntV(op(a, b))
      case _ => error("not a number")
    }
    def booVop(op : (BigInt, BigInt) => Boolean): (Value,Value) => Value = {
      case (IntV(a), IntV(b)) => BooleanV(op(a, b))
      case _ => error("not a number")
    }
    val intAdd = intVop(_ + _)
    val intMul = intVop(_ * _)
    val intDiv = intVop(_ / _)
    val intMod = intVop(_ % _)
    val booEq = booVop(_ == _)
    val booLt = booVop(_ < _)

    def malloc(a: Store): Addr= {
      maxAddress(a) +1
    }
    def maxAddress(a: Store): Addr= {
      a.keySet.+(0).max
    }*/
    inter(expr, Map(), Map())._1
    }
  } 
}

