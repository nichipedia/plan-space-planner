package com.realgood.planspace;

import edu.uno.ai.planning.Operator;
import edu.uno.ai.planning.Plan;
import edu.uno.ai.planning.Problem;
import edu.uno.ai.planning.TotalOrderPlan;
import edu.uno.ai.planning.logic.Bindings;
import edu.uno.ai.planning.ps.*;
import edu.uno.ai.planning.util.DirectedAcyclicGraph;
import edu.uno.ai.planning.util.ImmutableList;
import edu.uno.ai.planning.util.MinPriorityQueue;
import edu.uno.ai.planning.logic.Literal;

/**
 * @author Nicholas Moran
 * Created on 9/19/17.
 */
public final class PopSearch extends PlanSpaceSearch {
    private static MinPriorityQueue agenda;
    private static PartialStep start;

    public PopSearch(Problem problem) {
        super(problem);
        agenda = new MinPriorityQueue();
        agenda.push(this.root, this.root.flaws.length);
        start = this.root.steps.rest.first;
    }

    @Override
    public final Plan findNextSolution() {
        TotalOrderPlan plan = new TotalOrderPlan();
        while (!agenda.isEmpty()) {
            PlanSpaceNode node = (PlanSpaceNode)agenda.pop();
            if (node.flaws.length == 0) {
                for (PartialStep partial:node.orderings) {
                    if (partial.operator != null) { plan = plan.addStep(partial.makeStep(node.bindings)); }
                }
                return plan;
            }
            refine(node);
        }
        return null;
    }

    protected final void refine(PlanSpaceNode node) {
        Flaw flaw = selectFlaw(node.flaws);
        if (flaw instanceof OpenPreconditionFlaw) {
            OpenPreconditionFlaw precon = (OpenPreconditionFlaw)flaw;
            Literal literal = precon.precondition;
            for (Operator operator: root.problem.domain.operators) {
                PartialStep step = new PartialStep(operator);
                for (Literal effect:step.effects) {
                    if (effect.unify(literal, node.bindings) != null && node.orderings.add(step, precon.step) != null) {
                            addNewStep(node, step, precon, literal);
                    }
                }
            }

            for (PartialStep step:node.steps) {
                for(Literal effect:step.effects) {
                    if (effect.unify(literal, node.bindings) != null && node.orderings.add(step, precon.step) != null) {
                        addStep(node, step, precon, literal);
                    }
                }
            }
        } else if (flaw instanceof ThreatenedCausalLinkFlaw){
            ThreatenedCausalLinkFlaw threatenedLink = (ThreatenedCausalLinkFlaw) flaw;
            promote(node, threatenedLink);
            demote(node, threatenedLink);
        }
    }

    private Flaw selectFlaw(ImmutableList<Flaw> flaws) {
        for (Flaw flaw:flaws) {
            if (flaw instanceof ThreatenedCausalLinkFlaw) {
                return flaw;
            }
        }
        return flaws.first;
    }

    private void addStep(PlanSpaceNode node, PartialStep partialStep, OpenPreconditionFlaw precon, Literal literal) {
        DirectedAcyclicGraph orderings = node.orderings.add(partialStep, precon.step);
        CausalLink link = new CausalLink(partialStep, literal, precon.step);
        ImmutableList causalLinks = node.causalLinks.add(link);
        Bindings bindings = findBindings(node, partialStep, literal);
        ImmutableList flaws = addThreatenedCausalLinkFlaws(node.steps, orderings, causalLinks, node.flaws.remove(precon), bindings);
        PlanSpaceNode temp = node.expand(node.steps, bindings, orderings, causalLinks, flaws);
        agenda.push(temp, (double)temp.steps.length + (double)temp.flaws.length);
    }

    private void addNewStep(PlanSpaceNode node, PartialStep partialStep, OpenPreconditionFlaw precon, Literal literal) {
        ImmutableList flaws = node.flaws;
        if (!(node.steps.contains(partialStep))) {
            flaws = addOpenPreconditionFlaws(flaws, partialStep);
            ImmutableList steps = node.steps.add(partialStep);
            DirectedAcyclicGraph orderings = node.orderings.add(start, partialStep).add(partialStep, precon.step);
            CausalLink link = new CausalLink(partialStep, literal, precon.step);
            ImmutableList causalLinks = node.causalLinks.add(link);
            Bindings bindings = findBindings(node, partialStep, precon.precondition);
            flaws = addThreatenedCausalLinkFlaws(steps, orderings, causalLinks, flaws.remove(precon), bindings);
            PlanSpaceNode temp = node.expand(steps, bindings, orderings, causalLinks, flaws);
            agenda.push(temp, (double)temp.steps.length + (double)temp.flaws.length);
        }
    }

    private ImmutableList addOpenPreconditionFlaws(ImmutableList flaws, PartialStep partialStep) {
        for (Literal effect:partialStep.preconditions) {
            flaws = flaws.add(new OpenPreconditionFlaw(partialStep, effect));
        }
        return flaws;
    }

    private ImmutableList addThreatenedCausalLinkFlaws(ImmutableList<PartialStep> steps, DirectedAcyclicGraph orderings, ImmutableList<CausalLink> links, ImmutableList flaws, Bindings bindings) {
        for (CausalLink linkThreat:links) {
            for (PartialStep step : steps) {
                for (Literal effect : step.effects) {
                    Bindings unify = effect.unify(linkThreat.label.negate().substitute(bindings), bindings);
                    if (unify != null && orderings.add(linkThreat.tail, step) != null && orderings.add(step, linkThreat.head) != null) {
                        flaws = flaws.add(new ThreatenedCausalLinkFlaw(linkThreat, step));
                    }
                }
            }
        }
        return flaws;
    }

    private Bindings findBindings(PlanSpaceNode node, PartialStep partialStep, Literal precon) {
        Bindings bindings = node.bindings;
        for (Literal effect:partialStep.effects) {
                Bindings temp = effect.unify(precon, bindings);
                if (temp != null) {
                    bindings = temp;
                }
        }
        return bindings;
    }

    private static void promote(PlanSpaceNode node, ThreatenedCausalLinkFlaw threatenedLink) {
        DirectedAcyclicGraph orderings = node.orderings.add(threatenedLink.link.head, threatenedLink.threat);
        if (orderings != null) {
            PlanSpaceNode temp = node.expand(node.steps, node.bindings, orderings, node.causalLinks, node.flaws.remove(threatenedLink));
            agenda.push(temp, (double)temp.steps.length + (double)temp.flaws.length);
        }
    }

    private static void demote(PlanSpaceNode node, ThreatenedCausalLinkFlaw threatenedLink) {
        DirectedAcyclicGraph orderings = node.orderings.add(threatenedLink.threat, threatenedLink.link.tail);
        if (orderings != null) {
            PlanSpaceNode temp = node.expand(node.steps, node.bindings, orderings, node.causalLinks, node.flaws.remove(threatenedLink));
            agenda.push(temp,(double)temp.steps.length + (double)temp.flaws.length);
        }
    }
}
