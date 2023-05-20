package cs320

import Value._

object Implementation extends Template {
  def binOp(op: (Int,Int) => Int ) = {
    (l: Value, r: Value) => (l, r) match {
      case (NumV(l),NumV(r)) => NumV(op(l,r))
      case (l,r) => error(s"not both number: $l, $r")
    }
  }
  val numAdd = binOp(_ + _)
  val numSub = binOp(_ - _)

  def interp(expr: Expr): Value = {
    def aux(expr: Expr, env: Env): Value= expr match {
    case Num(num) => NumV(num)
    case Add(l,r) => numAdd(aux(l,env),aux(r,env))
    case Sub(left, right) => numSub(aux(left,env), aux(right,env))
    case Val(name,value,body) => aux(body, env + (name -> aux(value,env)))
    case Id(name) => env.getOrElse(name,error("free identifiers: $name"))
    case App(func,args) => aux(func, env) match {
        case CloV(params, body, envv) => {
          if (params.length != args.length) error("wrong arity")
          else {
            val l = args.map(aux(_, env))
            val arg= (params zip l)
            aux(body, envv ++ arg)
          }
        }
        case _ => error("not a closure")
      }
    case Fun(params, body) => CloV(params, body, env)
    case Rec(rec) => {
      RecV(rec.map {
        case (f,e) => (f, aux(e, env))
      })
    }
    case Acc(expr, name) => aux(expr, env) match {
      case RecV(rec) => rec.getOrElse(name, error("no such field: $name")) 
      case _ => error("not a record")
      }
    }
    aux(expr,Map())
  }

}
