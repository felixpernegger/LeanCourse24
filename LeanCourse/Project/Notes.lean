/- This serves as a note to the project.







-Try to prove the axioms given in euclid (if they are provable / make sense). This is very much advicable as any geometry theorem should be able to derived purely from that standpoint further on and not rely on complex numbers.

-For theorems proves with compelx number it might be best to first prove it for the special case of the unit circle
  and then prove it for general traingles / circles -/

--Finishing in_between stuff is important for introducing directed ration which will be needed for ceva and stuff later on
--Also i want to use in between stuff for uniqueness of circle center.
--Another thing eventually necessary (rather soone than later), is introduction of perpendicular lines.
--There are sever approaches on how to define them, we will se what will be best
/-
Also i have to look up the fact for perpeinduclar bisector (lol). That would give a cleaner proof
for circumcenter, although one could very realistically bruteforce it.

I still want to wait a while until I introduce angles, as they will be very painful.-/

--7.6k llines rn

/-I should probably reorder the files. Namely, Basic, Lines, Parallels, Perpendiculars, Triangles,
,*incoming* Orthocenter, Circles.
That would make much more sense for a variety of reasons.-/

--Alma 1Klaur 13.2 Fr 14.2 Korrektur evtl aufisch am 13.
--2klausur 18.3 korrektur 20.3
--test


--USE set INSTEAD OF let !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
--simp? is nice for simp only
--make small lemmas!!!
--maybe #in_imports  at bottom? dont forget rename and maybe look at rename_i
--#lint ?

--WRITE INSTANCE TO GET RID OF PADD AND PNEG
--instance : Add Point := ⟨padd⟩
--local (or different) ifix:65 " +' " => HAdd.hAdd



--MAYBE REWRITE THE PROOF OF THALES MEM; IT IS VERY SUS
