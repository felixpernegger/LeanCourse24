import LeanCourse.Project.Hilbert
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false

/-This project is about planar Euclidean Geometry defined via complex numbers.
Pretty much everything I did, I proved from scratch, i.e. did not use mathlib (only sometimes rarely for small numerical lemmas).

Therefore, a big part of the project is defining geomtric structures and proving elementary propositions about them,
which often seem quite trivial. Nonetheless, more advanced stuff was proved as well.-/

/-I originally set out to prove Feurbach's theorem (Incircle and Nine-Point-circle of a triangle are tangent) within this framweork,
however this turned out too be much too difficult for now, mainly because defining the incircle is quite problematic.-/

/-The entire project spans over 14.000 lines of code. I suspect much of this could be saved with more efficient code though, as there
are a few redundancies and so on.-/

/-Now a brief description of what every file does in the order of their dependancies:-/
/- # Basic.lean -/ --Introduces points, basic properties about them and what it means for points to be colinear (+ properties)
/- # Lines.lean -/ --Introduces lines (basically: Set of colinear points) and shows basic properties (i.e. there is a unique line between two (disjoint) points)
/- # Parallels.lean -/ --Introduces parallels. Lines are said to be parallel if one can be obtained by "shifting the other". This is proven to be equivalent as being the same or disjoint (tedious!). On top of that, the parallel postulate is proven.
/- # qObject.lean -/ --Rather short file mostly simplifying "notation", i.e. introduces a simplified function for taking two points to the line between them, not requiring them to be disjoint. No actual mathematical results are proven.
/- # Triangles.lean -/ --Introduces criangles (3 noncolinear points) and areas of three points / triangles. Furhtermore an important notion of a point being in between two others is introduced.
/- # Circles.lean -/ --Introduces circles and proves basic properties about them, i.e. uniqueness of radius and center
/- # Perpendiculars.lean -/ --Introduces perpendicular lines (and foot of a point on a line) and proves basic stuff about them, i.e. the corresponding "parallel postulate" for them or that being twice perpendicular is the same as being parallel.
/- # Pythagoras.lean -/ -- Proves Pythagoras theorem (not hard the way I defined geometry) and shows some direct consequences. Pythagoras theorem lates becomes quite useful for various tasks.
/- # Auxiliary.lean -/ --Small file doing nothing important. Mainly the notion of lying on the same side of a line and lying inside a triangle is introduced, however nothing important is being proved.
/- # Circumcircle.lean-/ --Three noncolinear points lie on a unique circle ! This result is proven via the usual characterization of the perpendicular bisector.
/- # Reflections.lean-/ --Introduces reflection along points and lines and proves stuff like "reflecting twice" goves the original.
/- # Lineartrans.lean-/ --A not-so-interesting file showing that under x ↦ a*x + b for a ≠ 0, pretty much every geomtric structure is preserved. I only used this in very few occassions, but this would be a key technique necessary to proving complicated stuff analytically, as it basically allows us saying "wlog". This could be done via group actions, but I was too lazy.
/- # Tangents.lean-/ --Introduces tangents to circles and shows stuff like uniqueness of a tangent to a fixed point on the circle. Pythagoras theorem was needed for this.
/- # CTangent.lean-/ --Introduces the notion of two circles being tangent to each other and proves consequences about colineairty and radii etc.
/- # Powpoint.lean-/ --Introduces the power of a point in respect to the circle. In particular, for two nonconcentric circles the ste of points with same power to them form a line, the "Powline" as I called it, which is very useful.
/- # Angles.lean-/ --Introduces angles and proves basic stuff. I am not extremely happy with how everything was done, but they do the job just fine. Angles are only occassionally from this point on.
/- # Thales.lean-/ --Proves both directions of Thales theorem. For the first one a (in Lean) painful angle chase was used, for converse an argument avoiding angles I thought of (via parallel lines / rectangles).
/- # Orthocenter.lean-/ --Proves the existence of the orthocenter (as the intersections of the altidues). This is really not that trivial: I used (converse of) Thales theorem combined with power of points, giving a neat proof.
/- # Similar.lean-/ --Introducing similar triangles in several ways (orientation or not matters!) via functions described in Lineartrans.lean. Some characterizations, like angles being the same implying the triangles to be similar.
/- # Ceva.lean -/ --By far the coolest thing I proved: Ceva's theorem, both directions in what is probably the most general form for the planar form. Proof was mainly the standard argument with areas, which while simples, is a bit annoying to set up. 2.7k lines (by far the largest file)

/- # Incircle.lean, Hilbert.lean-/ -- are (very!) unfinished and do not contain anything relevant.

/- Sometimes theorems are not at the place they logically should be located due to various reasons, but this is not very frequent.-/

/-A small collection of some of the main/most interesting results I obtained:-/

#check colinear_trans --Basically: being colinear is transitive. This was the most central and hardest piece setting up the geometry.
#check parallel_def -- Being parallel is equivalent to being the same or not sharing a point (to appreciate this, one might want to check out my definition of Parallel)
#check parallel_postul
