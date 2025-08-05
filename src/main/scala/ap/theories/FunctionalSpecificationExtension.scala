package ap.theories

import ap.parser._
import ap.parser.IExpression.v
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.types.MonoSortedIFunction
import ap.parser.IExpression.all
import ap.parser.SMTParsingUtils.asTerm
import ap.parser.SMTTypes.SMTType
import ap.parser.IExpression.Predicate
import ap.parser.IExpression.Quantifier
import ap.terfor.conjunctions.Quantifier.ALL
import ap.parser.SymbolCollector.variables
import ap.parser.IExpression.Sort
import ap.theories.RecursiveADTExtension
import ap.parameters.Param.ABBREV_LABELS.defau
import ap.util.Debug.AC_ADT
import ap.util.Debug

class FunctionalSpecificationExtension private (
                            axiomBody: IFormula,
                            catamorphicTheories: Set[RecursiveADTExtension],
                            triggers: Set[ITerm],
                            quantifyingVariables: Seq[IVariable]
  ) extends SMTLinearisableTheory {

  import FunctionalSpecificationExtension._

  override val dependencies: Iterable[Theory] = catamorphicTheories ++ catamorphicTheories.flatMap(_.dependencies)

  val functions = List.empty[IFunction] // the theory provides axioms, but no new functions

  val definitionAxiom = {
    val sorts = quantifyingVariables.map(_.sort)
    all(
      sorts,
      ITrigger(
        triggers.toSeq,
        axiomBody
      )
    )
  }

  val (predicates, axioms, order, functionMap) = 
    Theory.genAxioms(
      theoryFunctions = functions,
      theoryAxioms = definitionAxiom,
      otherTheories = dependencies.toSeq
    )

  val functionalPredicates = Set.empty[Predicate]

  val functionPredicateMapping = functionMap.toSeq

  def plugin = None

  val totalityAxioms = Conjunction.TRUE

  // trigger other axioms based on catamorphism
  val triggerRelevantFunctions = Set.empty[IFunction]

  val predicateMatchConfig = Map.empty

  override def isSoundForSat(theories: Seq[Theory], config: Theory.SatSoundnessConfig.Value): Boolean = {
    true
  }

  ////////////////////////////////////////////////////////////////////
  
  override def printSMTDeclaration: Unit = 
    // just print this as a normal assertion
    SMTLineariser.printWithDecls(Seq(definitionAxiom))
  
  ////////////////////////////////////////////////////////////////////

  TheoryRegistry.register(this)
  
}

object FunctionalSpecificationExtension {
  private val AC = AC_ADT

  case class MalformedSpecificationAxiom private (msg: String) extends Exception(msg)

  /**
    * A decomposition of a single-invocation axiom into its components.
    *
    * @param axiomBody the body of the axiom, without quantifiers
    * @param theories [non-empty] recursive extensions for which the axiom is a single-invocation axiom
    * @param triggers [non-empty] the triggers present in and inferred from the axiom
    * @param variables the variables quantified in the axiom
    */
  case class SingleInvocationDecomposition private (
    axiomBody: IFormula,
    theories: Set[RecursiveADTExtension],
    triggers: Set[ITerm],
    variables: Seq[IVariable]
  ) {
    Debug.assertInt(AC_ADT, theories.nonEmpty, "No theories in a single-invocation axiom decomposition")
    Debug.assertInt(AC_ADT, triggers.nonEmpty, "No triggers in a single-invocation axiom decomposition")
  }

  /**
    * Attempt to construct a functional specification extension from a formula,
    * assuming that it is a single-invocation axiom. Throws an exception if the
    * axiom is malformed.
    * 
    * See [[decomposeSingleInvocationAxiom]] for details.
    *
    * @param axiom
    * @return
    */
  def apply(axiom: IFormula): FunctionalSpecificationExtension = {
    val decomposition = decomposeSingleInvocationAxiom(axiom)
      .getOrElse(throw MalformedSpecificationAxiom("Not a valid single-invocation axiom"))

    apply(decomposition)
  }

  /**
    * Construct and register a functional specification extension from a
    * decomposed single-invocation axiom. See
    * [[decomposeSingleInvocationAxiom]].
    *
    * @param decomposition
    * @return
    */
  def apply(decomposition: SingleInvocationDecomposition): FunctionalSpecificationExtension = {
    new FunctionalSpecificationExtension(
      axiomBody = decomposition.axiomBody,
      catamorphicTheories = decomposition.theories,
      triggers = decomposition.triggers,
      quantifyingVariables = decomposition.variables
    )
  }

  /**
    * Collect all the function applications in a formula.
    */
  private object FunctionCollectingVisitor extends CollectingVisitor[Unit, Vector[IFunApp]] {
    def apply(formula: IFormula): Vector[IFunApp] = {
      visit(formula, ())
    }

    def postVisit(t: IExpression, arg: Unit, subres: Seq[Vector[IFunApp]]): Vector[IFunApp] = {
      var res = t match {
        case app: IFunApp => Vector(app)
        case _ => Vector.empty
      }

      for (r <- subres) res ++= r
      
      res
    }
  }

  /**
    * Attempt to decompose a formula as a single-invocation axiom.
    *
    * A formula is a single-invocation axiom wrt a function `f` if it is of the
    * form:
    *
    *   ∀ x_1, x_2, ..., x_n. φ[x_1, x_2, ..., x_n, f(x_1, x_2, ..., x_n)]
    *
    * If found to be a single-invocation axiom for any recursive extensions
    * `{f_i}`, returns the list of their invocations and theories.
    *
    * On correspondence of single-invocation axioms to postconditions:
    *
    * https://doi.org/10.1007/978-3-642-18275-4_20\
    * 
    * Returns an option as the case of it being a single-invocation axiom
    * of no theories is special.
    *
    * @return optionally, a non-empty list of recursive extension theories for
    * which the formula is a single-invocation axiom, and the list of existing
    * triggers
    */
  def decomposeSingleInvocationAxiom(axiom: IFormula): Option[SingleInvocationDecomposition] = {
    
    // strip the top-level universal quantifiers from a formula and collect the
    // quantifying variables
    def stripQuantifiers(formula: IFormula): (Seq[IVariable], IFormula) = {
      @annotation.tailrec
      def accumulateSorts(formula: IFormula, acc: List[Sort] = List.empty): (List[Sort], IFormula) =
        formula match {
          case ISortedQuantified(ALL, s, body) =>
            accumulateSorts(body, s +: acc)
          case _ => (acc, formula)
        }
      
      val (sorts, strippedBody) = accumulateSorts(formula)
      val sortedVars = sorts.iterator.zipWithIndex.map{ case (s, i) => v(i, s) }.toSeq

      (sortedVars, strippedBody)
    }

    // check if the function application is applied to exactly a set of
    // variables modulo permutation
    def isOpenInvocation(app: IFunApp, vars: Set[IVariable]): Boolean = {
      val IFunApp(f, args) = app
      
      // (exactly) all variables are used
      f.arity == vars.size && args.toSet == vars
    }

    if (variables(axiom).nonEmpty) {
      // not a closed axiom
      None
    } else {
      // strip the quantifiers and triggers present
      val (vars, rawBody) = stripQuantifiers(axiom)
      val (defaultTriggers, body) = rawBody match {
        case ITrigger(triggers, b) => (triggers, b)
        case b => (Seq.empty, b)
      }

      val varSet = vars.toSet

      // collect all function applications in the body
      // group them by the functor
      // filter for single-invocation functors
      val funApps = 
        FunctionCollectingVisitor(body)
          .groupBy(_.fun)
          .filter{ case (fun, apps) => 
            apps.length == 1 && apps.forall(isOpenInvocation(_, varSet))
          }

      // for each such functor, if its theory is a recursive extension, store
      // the theory and keep the invocation as a trigger
      val (theories, triggers) =
        funApps.foldLeft((Set.empty[RecursiveADTExtension], Set.empty[ITerm])) {
          case ((theories, triggers), (fun, apps)) =>
            val app = apps.head
            val theoryOpt = TheoryRegistry.lookupSymbol(fun)

            theoryOpt match {
              case Some(t : RecursiveADTExtension) =>
                (theories + t, triggers + app)
              case None =>
                (theories, triggers)
            }
        }

      Some(SingleInvocationDecomposition(
        body,
        theories,
        triggers ++ defaultTriggers,
        vars
      ))
    }

  }
}

