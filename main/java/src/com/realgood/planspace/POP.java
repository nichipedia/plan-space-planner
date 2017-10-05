package com.realgood.planspace;

/**
 * Created by NicholasMoran on 9/19/17.
 */

import edu.uno.ai.planning.Problem;
import edu.uno.ai.planning.ps.PlanSpacePlanner;
import edu.uno.ai.planning.ps.PlanSpaceSearch;

public class POP extends PlanSpacePlanner {
    public POP() { super("nmoran_THA_POP_DADDEH"); }

    public PlanSpaceSearch makeSearch(Problem problem) {
        return new PopSearch(problem);
    }
}
