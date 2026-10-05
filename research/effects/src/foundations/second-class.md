# Second-class values

A second-class value can be passed down into calls but cannot be returned, stored or captured by a first-class closure. Its lifetime is the frame's, so in BoLo terms it is a lend for the call.

Making capabilities and `resume` second-class gives:
- **effect safety and capability escape** as scoping (System C);
- **no accidental handling** by construction;
- **effect polymorphism without row variables** for callbacks that are only called, which is the no-colouring story;
- **continuations that cannot outlive their lends,** and can be allocated on the stack.

**The cost:** storing anything effectful needs a box with a lifetime bound (OQ-28, Unit 5).

**Our evidence:** `experiments/SecondClass` (`handleAt_compatC`, Core σ=[]), and decision 57's tunnelled rows.
