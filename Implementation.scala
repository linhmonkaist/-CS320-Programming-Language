package cs320

object Implementation extends Template {

  // apply a binary numeric function on all the combinations of numbers from
  // the two input lists, and return the list of all the results
  def binOp(
    op: (Int, Int) => Int,
    ls: List[Int],
    rs: List[Int]
  ): List[Int] = ls match {
    case Nil => Nil
    case l :: rest =>
      def f(r: Int): Int = op(l,r)
      rs.map(f) ++ binOp(op, rest, rs)
  }

  def interp(expr: Expr): List[Int] = {
    def aux(expr: Expr,env: Map[String, List[Int]]): List[Int]= expr match {
      case Num(values) => values
      case Add(left,right) => binOp((x,y) => x+y, aux(left,env), aux(right,env))
      case Sub(left,right) => binOp((x,y) => x-y, aux(left,env), aux(right,env))
      case Val(name,expr,body) => aux(body, env + (name -> aux(expr, env)))
      case Id(value) => env.getOrElse(value,error("free identifier"))
      case Min(l,m,r) => {
        val v= binOp( (x,y) => x.min(y), aux(l,env),aux(m,env))
        binOp(_ min _ , v, aux(r, env))
      }
      case Max(l,m,r) => if ((aux(l,env).head >= aux(m, env).head) & (aux(l,env).head >= aux(r,env).head)) {aux(l,env);}
                            else {
                              if ((aux(m, env).head > aux(l, env).head) & (aux(m, env).head >= aux(r, env).head)) {aux(m,env);}
                              else {(aux(r, env));}
                            }
    }
    aux(expr, Map())
  }
}
