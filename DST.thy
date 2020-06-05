theory DST
  imports Main "~~/src/HOL/Analysis/Elementary_Topology"
begin
lemma 
  fixes U :: "'a :: second_countable_topology set"
  shows "seq_compact U \<longleftrightarrow> compact U"
end
