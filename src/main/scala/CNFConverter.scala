import scala.collection.mutable
import scala.collection.mutable.{HashMap, ListBuffer, Set}

class CNFConverter {

  val S = new Solver()
  val map: HashMap[Int, Literal] = new HashMap()
  val processedClause: Set[Int] = Set()
  var count = 0
  val variableMap: HashMap[Expr, Literal] = new HashMap()
  var resultMap: HashMap[Variable, Boolean] = new HashMap()


  def applyCNFRules(e: List[Expr]): Unit = {

    if(e.size<=0)
      (false, Option(resultMap.toMap))
    else {

      try {
        generateFreshClause(e)
        S.addClause(map.get(e.head.hashCode).get)

      }catch {
        case _:Throwable => println("empty clause exception")
        //(false, Option(resultMap.toMap))
      }

    }

    def generateFreshClause(e: List[Expr]): Unit = {
      if(!e.isEmpty) {
        val ex = e.head

        if (map.get(ex.hashCode) == None) {
          map.put(ex.hashCode, createAndAddLiteral(count + 1))
          count += 1
        }

        ex match {
          case Variable(arg) => {
            variableMap.put(Variable(arg), map.get(ex.hashCode).get)
          }
          case Not(args) => {

            generateFreshClause(List(args))
            introduceFreshVariableNot(ex, List(args))
          }
          case And(args) => {
            for (exp <- args) {
              generateFreshClause(List(exp))
            }
            introduceFreshVariableAnd(ex, args)

          }
          case Or(args) => {
            for (exp <- args) {
              generateFreshClause(List(exp))
            }
            introduceFreshVariableOr(ex, args)
          }
          case BoolLit(value) => introduceFreshVariableBoolean(ex)
          case _ => Nil
        }
      }
      //S.addClause(Literal.create(map.get(ex.hashCode).get))
    }

    def introduceFreshVariableBoolean(expr: Expr): Unit ={
      if(processedClause.contains(expr.hashCode)) return
      val freshLiteral = map.get(expr.hashCode).get
      expr match {
        case BoolLit(true)=> {
          S.addClause(freshLiteral)
        }
        case BoolLit(false)=> {
          S.addClause(~freshLiteral)
        }
      }
      processedClause+=expr.hashCode
    }

    def introduceFreshVariableNot(expr: Expr, exprs: List[Expr]): Unit = {
      /*if(processedClause.contains(expr.hashCode))
        return*/
      S.addClause(~map.get(expr.hashCode).get, ~map.get(exprs.head.hashCode).get)
      S.addClause(map.get(expr.hashCode).get, map.get(exprs.head.hashCode).get)
      //processedClause+=expr.hashCode
    }

    def introduceFreshVariableAnd(expr: Expr, exprs: List[Expr]): Unit = {
      /*if(processedClause.contains(expr.hashCode))
        return*/
      var list = new ListBuffer[Literal]()
      val freshLiteral = map.get(expr.hashCode).get
      list += freshLiteral
      for (exp <- exprs) {
        val currLit = map.get(exp.hashCode).get
        list += ~currLit
        S.addClause(currLit, ~freshLiteral)

      }
      S.addClause_(list.toList)
      //processedClause+=expr.hashCode
    }

    def introduceFreshVariableOr(expr: Expr, exprs: List[Expr]): Unit = {
      /*if(processedClause.contains(expr.hashCode))
        return*/
      var list = new ListBuffer[Literal]()
      val freshLiteral = map.get(expr.hashCode).get

      list += ~freshLiteral
      for (exp <- exprs) {
        val currLit = map.get(exp.hashCode).get
        list += currLit
        S.addClause(~currLit, freshLiteral)

      }
      S.addClause_(list.toList)
      //processedClause+=expr.hashCode
    }

    def createAndAddLiteral(value: Int): Literal = {
      Literal.create(value)
    }


  }

  def callSolver(): (Boolean, Option[Map[Variable,Boolean]])={
    val solverResult = S.solve()
    if (solverResult) {
      for ((key, value) <- variableMap) {
        if (key.isInstanceOf[Variable])
          resultMap.put(key.asInstanceOf[Variable], S.modelValue(value))
      }

    }
    (solverResult, Option(resultMap.toMap))
  }
}