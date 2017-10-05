package com.realgood.planspace;

import edu.uno.ai.planning.*;
import edu.uno.ai.planning.logic.Bindings;
import edu.uno.ai.planning.ps.*;
import edu.uno.ai.planning.util.DirectedAcyclicGraph;
import edu.uno.ai.planning.util.ImmutableList;
import edu.uno.ai.planning.util.MinPriorityQueue;
import edu.uno.ai.planning.logic.Literal;

/**
 * Created by NicholasMoran on 9/19/17.
 */
public class PopSearch extends PlanSpaceSearch {
    public static MinPriorityQueue agenda = new MinPriorityQueue();
    public static PartialStep start;
    public static PartialStep end;

    public PopSearch(Problem problem) {
        super(problem);
        agenda.push(this.root, this.root.flaws.length + this.root.steps.length);
        end = this.root.steps.first;
        start = this.root.steps.rest.first;
    }

    @Override
    public Plan findNextSolution() {
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
        System.out.println("Returned Null");
        return null;
    }

    public void refine(PlanSpaceNode node) {
        //Ask do i need to iterate over all effects in a step....probably....
        Flaw flaw = node.flaws.first;
        if (flaw instanceof OpenPreconditionFlaw) {
            OpenPreconditionFlaw precon = (OpenPreconditionFlaw)flaw;
            System.out.println("Precondition.." + precon);
            DirectedAcyclicGraph orderings = node.orderings;
            System.out.println("yah");
            Literal literal = precon.precondition;
            PartialStep datStep = null;
            for (PartialStep step:node.steps) {
                for(Literal effect:step.effects) {
                    Bindings unifyCheck = effect.unify(literal, node.bindings);
                    if (unifyCheck != null) {
                        System.out.println("uno");
                        datStep = step; }
                }
            }
            if (datStep != null) {
                System.out.println("Dat step " + datStep);
                CausalLink link = new CausalLink(datStep, literal, precon.step);
                orderings = orderings.add(datStep, precon.step);
                System.out.println("Orderings for a step.." + orderings);
                ImmutableList causalLinks = node.causalLinks.add(link);
                PlanSpaceNode temp = node;
                ImmutableList flaws = node.flaws;
                System.out.println("yes");
                Bindings bindings = findBindings(node, datStep, literal);
                flaws = addThreatenedCausalLinkFlaws(node, flaws, link, bindings);
                temp = temp.expand(node.steps, bindings, orderings, causalLinks, flaws.remove(precon));
                System.out.println(temp);
                agenda.push(temp, temp.steps.length + temp.flaws.length);
            } else {
                //operators are found in domain object of problem.
                //how do I create a new step...
                PartialStep partialStep = createPartialStep(node, literal);
                System.out.println("Partial here: " + partialStep);
                CausalLink link = new CausalLink(partialStep, literal, precon.step);
                ImmutableList causalLinks = node.causalLinks.add(link);
                PlanSpaceNode temp = node;
                ImmutableList flaws = temp.flaws.remove(precon);
                flaws = addOpenPreconditionFlaws(flaws, partialStep);
                Bindings bindings = findBindings(node, partialStep, literal);
                flaws = addThreatenedCausalLinkFlaws(node, flaws, link, bindings);
                ImmutableList steps = node.steps.add(partialStep);
                orderings = orderings.add(start, partialStep);
                orderings = orderings.add(partialStep, precon.step);
                temp = node.expand(steps, bindings, orderings, causalLinks, flaws);
                agenda.push(temp, temp.steps.length + temp.flaws.length);
            }
        } else if (flaw instanceof ThreatenedCausalLinkFlaw){
            ThreatenedCausalLinkFlaw threatenedLink = (ThreatenedCausalLinkFlaw) flaw;
            promote(node, threatenedLink);
            demote(node, threatenedLink);
        } else {
            System.out.println("This flaw" + flaw);
        }
    }

    public ImmutableList addOpenPreconditionFlaws(ImmutableList flaws, PartialStep partialStep) {
        for (Literal effect:partialStep.preconditions) {
            flaws = flaws.add(new OpenPreconditionFlaw(partialStep, effect));
        }
        return flaws;
    }

    public ImmutableList addThreatenedCausalLinkFlaws(PlanSpaceNode node, ImmutableList flaws, CausalLink link, Bindings bindings) {
        for (PartialStep step:root.steps) {
            for (Literal effect: step.effects) {
                Bindings unify = effect.unify(link.label.negate(), bindings);
                if (unify != null) {
                    System.out.println("Flaw");
                    flaws = flaws.add(new ThreatenedCausalLinkFlaw(link, step));
                }
            }
        }
        return flaws;
    }

    public Bindings findBindings(PlanSpaceNode node, PartialStep partialStep, Literal precon) {
        Bindings bindings = node.bindings;
        Bindings temp = bindings;
        System.out.println("Pre-bindings");
        for (Literal effect:partialStep.effects) {
                temp = effect.unify(precon, bindings);
                if (temp != null) {
                    System.out.println("Bindgins");
                    bindings = temp;
                }
        }
        return bindings;
    }

    public PartialStep createPartialStep(PlanSpaceNode node, Literal literal) {
        for (Operator operator: root.problem.domain.operators) {
            PartialStep step = new PartialStep(operator);
            for (Literal effect:step.effects) {
                Bindings unify = effect.unify(literal, node.bindings);
                if (unify != null) {
                    return step;
                }
            }
        }
        return null;
    }

    public static void promote(PlanSpaceNode node, ThreatenedCausalLinkFlaw threatenedLink) {
        DirectedAcyclicGraph orderings = node.orderings.add(threatenedLink.link.head, threatenedLink.threat);
        if (orderings != null) {
            PlanSpaceNode temp = node.expand(node.steps, node.bindings, orderings, node.causalLinks, node.flaws.remove(threatenedLink));
            agenda.push(temp, temp.steps.length + temp.flaws.length);
        }
    }

    public static void demote(PlanSpaceNode node, ThreatenedCausalLinkFlaw threatenedLink) {
        DirectedAcyclicGraph orderings = node.orderings.add(threatenedLink.threat, threatenedLink.link.tail);
        if (orderings != null) {
            PlanSpaceNode temp = node.expand(node.steps, node.bindings, orderings, node.causalLinks, node.flaws.remove(threatenedLink));
            agenda.push(temp,temp.steps.length + temp.flaws.length);
        }
    }
}
