# MODAL LOGIC
extends "the usual logic"
\phi, \psi ::= P | T | \bot | \phi \and \psi | \phi \or \psi | \phi \implies \psi

Special logics have extra operators/formulas:
all from the above + 
    square \phi
    diamond \phi


## Modal logic (S4)

What do I need to do:
- define datatype Formula from before with modalities
- define the semantics of \phi; the interpretation
- validate some axioms/tautologies, like
-- kvadrat \phi \implies kvadrat kvadrat \phi
    to se dokaze na tak nacin:
        \forall w. [| kvadrat \phi \implies kvadrat kvadrat \phi |] (w)
-- kvadrat \phi \implies \phi
        podobno kot zgori


In the last exercises [[ \phi ]]_\etha : Env \to Bool   or
In the last exercises [[ \phi ]] : Env \to HProp

In general modal logic:
(W, R, V)   a Kripke frame  ??
W - set of worlds/time
R - relation on W (has to be reflexive and transitive)
L - map: W -> (AtomicFormulas -> HProp) = P(AtomicFormulas)  (to je labeling function)

Interpretation:

[| \phi |]_(W, R, L) : W  -> HProp  (Dokaz je odvisen od tega v katerem svetu ga interpretiramo)

Poglej si:
Kripke semantics (of modal logic)

na spletu je tak: w ||- \phi, na vajah smo pisali: [| \phi |] (w) oboje je isto

Najbolj glavna stvar je interpretacija teh novih stvari: kvadratka in diamanta
box of \psi holds in world x if it holds in all worlds that we can go to from x
diamond of \psi holds in world x if it holds in any world that we can go to from x



! poglej si lecture notes

last weeks lecture
semantics.agda
parametrize

## Temporal logic (LTL = linear time logic)