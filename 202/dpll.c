#include <stdio.h>

typedef struct literal info{
int is assigned;
int n occur;
int * lit in clauses;
int * lit in clause locs;
int is unit;
int antecedent clause;
}literal info;
literal info linfo[MAX VARS][2];

typedef struct clause info{
int * literals;
int current length;
int original length;
int is satisfied;
int binary code;
int current ucl;
}clause info;
clause info * clauses;
int n clause, r clauses;

typedef struct changes info{
int clause index;
int literal index;
}changes info;
changes info changes[MAX CLAUSES];
unsigned int changes index;
unsigned int n changes[MAX VARS][2];

typedef struct assign info{
int type;
int depth;
int decision;
}assign info;
assign info assign[MAX VARS];

void SetVar(int v);
void UnSetVar(int v);
int dpll();
int compute_resolvent(int x, int a, int b, int & len, int limit);
int get_restricted_resolvent(int x, int limit);
int subsumable(int j, int k);
int preprocess_subsume();
int preprocess();
int add_a_clause_to_formula(int C[], int n);
int clause_present(int C[], int n);
inline int GetLiteralDLCS();

void SetVar(int v){
  register int i;
  register int p = abs(v), q = (v>0) ? SATISFIED : SHRUNK;
  for(i=0; i<linfo[p][q].n_occur; ++i){
    register int j = linfo[p][q].lit_in_clauses[i];
    if(clauses[j].is_satisfied) continue;
    clauses[j].is_satisfied = YES;
    --r_clauses;
    changes[changes_index++].clause_index = j;
    n_changes[depth][SATISFIED]++;
  }
  q = !q;
  for(i=0; i<linfo[p][q].n_occur; ++i){
    register int j = linfo[p][q].lit_in_clauses[i];
    if(clauses[j].is_satisfied) continue;
    register int k = linfo[p][q].lit_in_clause_locs[i];
    --clauses[j].current_length;
    clauses[j].binary_code -= ((1 << k));
    changes[changes_index].clause_index = j;
    changes[changes_index++].literal_index = k;
    n_changes[depth][SHRUNK]++;
    if(clauses[j].current_length == 1){
      register int loc = int(log2(clauses[j].binary_code));
      register int w = clauses[j].literals[loc];
      register int s = abs(w), t = (w>0) ? SATISFIED : SHRUNK;
      linfo[s][t].antecedent_clause = j;
      if(linfo[s][(!t)].is_unit == YES){
        contradictory_unit_clauses = TRUE;
        conflicting_literal = w;
      }
      else if(linfo[s][t].is_unit == NO){
        gucl_stack[n_gucl] = clauses[j].current_ucl = w;
        linfo[s][t].is_unit = YES;
        ++n_gucl;
      }
    }
  }
  if(depth && backtrack_level == depth-1) ++backtrack_level;
  ++depth;
  linfo[p][SATISFIED].is_assigned = YES;
  linfo[p][SHRUNK].is_assigned = YES;
}

void UnSetVar(int v){
  register int i;
  register int p = abs(v), q = (v>0) ? SATISFIED : SHRUNK;
  --depth;
  if(depth && backtrack_level == depth) --backtrack_level;
  while(n_changes[depth][SHRUNK]){
    --n_changes[depth][SHRUNK];
    register int j = changes[--changes_index].clause_index;
    register int k = changes[changes_index].literal_index;
    ++clauses[j].current_length;
    if(clauses[j].current_length == 2){
      int s = abs(clauses[j].current_ucl);
      int t = (clauses[j].current_ucl > 0) ? SATISFIED : SHRUNK;
      linfo[s][t].is_unit = NO;
      clauses[j].current_ucl = 0;
    }
    clauses[j].binary_code += ((1 << k));
  }
  while(n_changes[depth][SATISFIED]){
    --n_changes[depth][SATISFIED];
    register int j = changes[--changes_index].clause_index;
    clauses[j].is_satisfied = NO;
    ++r_clauses;
  }
  linfo[p][SATISFIED].is_assigned = NO;
  linfo[p][SHRUNK].is_assigned = NO;
}

int dpll(){
  int * lucl_stack = NULL;
  register unsigned int n_lucl = 0;
  while(1){
    if(contradictory_unit_clauses){
      icl_cnt = 0;
      int cl = abs(conflicting_literal);
      impl_clauses[icl_cnt++] = linfo[cl][SATISFIED].antecedent_clause;
      impl_clauses[icl_cnt++] = linfo[cl][SHRUNK].antecedent_clause;
      assign[cl].decision = ASSIGN_NONE;
      while(n_lucl){
        UnSetVar(lucl_stack[--n_lucl]);
        register int s = abs(lucl_stack[n_lucl]);
        register int t = lucl_stack[n_lucl]>0 ? TRUE : FALSE;
        impl_clauses[icl_cnt++] = linfo[s][t].antecedent_clause;
        assign[s].type = UNASSIGNED;
        assign[s].decision = ASSIGN_NONE;
      }
      contradictory_unit_clauses = FALSE;
      free(lucl_stack);
      n_gucl = 0;
      return UNSAT;
    }
    else if (n_gucl){
      lucl_stack = (int*)realloc(lucl_stack,(n_lucl+1)*sizeof(int));
      register int implied_lit = gucl_stack[--n_gucl];
      lucl_stack[n_lucl++] = implied_lit;
      assign[abs(implied_lit)].type = implied_lit>0 ? TRUE : FALSE;
      assign[abs(implied_lit)].decision = ASSIGN_IMPLIED;
      SetVar(implied_lit);
      n_units++;
    }
    else break;
  }
  if(!r_clauses) return SAT; register int v = GetLiteral2SJW();

  for(int i=1; i<=n_vars; ++i){
    int x, y, u, C;
    x = y = 0;
    if(assign[i].decision == ASSIGN_NONE){
      u = 0;
      for(int j=0; j<linfo[i][SATISFIED].n_occur; ++j){
        C = linfo[i][SATISFIED].lit_in_clauses[j];
        x += 1-clauses[C].is_satisfied;
      }
      for(int j=0; j<linfo[i][SHRUNK].n_occur; ++j){
        C = linfo[i][SHRUNK].lit_in_clauses[j];
        y += 1-clauses[C].is_satisfied;
      }
      if(x && !y) u = i;
      if(y && !x) u = -i;
      if(u){
        ml_stack = (int*) realloc(ml_stack,(n_ml+1)*sizeof(int));
        ml_stack[n_ml++] = u;
        assign[abs(u)].type = u>0 ? TRUE : FALSE;
        assign[abs(u)].depth = depth;
        assign[abs(u)].decision = ASSIGN_IMPLIED;
        SetVar(u);
      }
    }

  assign[abs(v)].type = v > 0 ? TRUE : FALSE;
  assign[abs(v)].depth = depth;
  assign[abs(v)].decision = ASSIGN_BRANCHED;
  SetVar(v);
  if(dpll()) return SAT;
  UnSetVar(v);
  assign[abs(v)].decision = ASSIGN_NONE;
  register int max_depth = 0, i, j, k, m, left = FALSE;
  if(icl_cnt){
    while(icl_cnt){
      i = impl_clauses[--icl_cnt];
      k = clauses[i].original_length;
      for(j=0; j < k; ++j){
        m = abs(clauses[i].literals[j]);
        if(assign[m].decision == ASSIGN_BRANCHED &&
          assign[m].depth > max_depth)
          max_depth = assign[m].depth;
        }
      }
      left = TRUE;
    }
    ++n_backtracks;
    if(backtrack_level >= depth-1){
      assign[abs(v)].type = !assign[abs(v)].type;
      assign[abs(v)].decision = ASSIGN_IMPLIED;
      SetVar(-v);
      if(dpll()) return SAT;
      UnSetVar(-v);
      assign[abs(v)].type = UNASSIGNED;
      assign[abs(v)].decision = ASSIGN_NONE;
      if(left && icl_cnt){
        while(icl_cnt){
          i = impl_clauses[--icl_cnt];
          k = clauses[i].original_length;
          for(j=0; j < k; ++j){
            m = abs(clauses[i].literals[j]);
            if(assign[m].decision == ASSIGN_BRANCHED &&
              assign[m].depth > max_depth)
              max_depth = assign[m].depth;
            }
          }
          if(max_depth < backtrack_level) backtrack_level = max_depth;
        }
      }

      while(n_ml){
        int u = ml_stack[--n_ml];
        UnSetVar(u);
        assign[abs(u)].type = UNASSIGNED;
        assign[abs(u)].decision = ASSIGN_NONE;
      }

      icl_cnt = 0;
      while(n_lucl){
        int z = lucl_stack[--n_lucl];
        UnSetVar(z);
        assign[abs(z)].type = UNASSIGNED;
        assign[abs(z)].decision = ASSIGN_NONE;
      }
      free(lucl_stack);
      contradictory_unit_clauses = FALSE;
      return UNSAT;
    }

int compute_resolvent(int x, int a, int b, int & len, int limit){
  register int j, k;
  int * check = (int *)calloc(n_vars+1, sizeof(int));
  int found = FALSE;
  int res_size = 0;
  int C[2] = {a, b};
  for(j=0; j<2; ++j){
    for(k=0; k<clauses[C[j]].original_length; ++k){
      register int w = abs(clauses[C[j]].literals[k]);
      if(w == x) continue;
      else if(check[w] == clauses[C[j]].literals[k]) continue;
      else if(check[w] == -clauses[C[j]].literals[k]){
        free(check); return FALSE;
      }
      else if(assign[abs(clauses[C[j]].literals[k])].decision!= ASSIGN_NONE) continue;
      else if(check[w] == 0){
        check[w] = clauses[C[j]].literals[k];
        resolvent[res_size++] = clauses[C[j]].literals[k];
        if(res_size > limit){
          free(check); return FALSE;
        }
      }
    }
  }
  len = res_size;
  free(check);
  return TRUE;
}

int get_restricted_resolvent(int x, int limit){
  register int i, j, k, a, b, res_length;
  int found;
  changes_occured = FALSE;
  for(i=0; i<linfo[x][SATISFIED].n_occur; ++i){
    a = linfo[x][SATISFIED].lit_in_clauses[i];
    if(clauses[a].is_satisfied == NO){
      for(j=0; j<linfo[x][SHRUNK].n_occur; ++j){
        b = linfo[x][SHRUNK].lit_in_clauses[j];
        if(clauses[b].is_satisfieinline int GetLiteralDLCS(){
d == NO){
          found = compute_resolvent(x, a, b, res_length, limit);
          if(found){
            if(resolvent_added < n_resolvents_threshold){
              resolvent_added +=
              add_a_clause_to_formula(resolvent, res_length);
              changes_occured = TRUE;
            }
            else return -1;
          }
        }
      }
    }
  }
  return -1;
}

int subsumable(int j, int k){
  register int i;
  int * check = (int *) calloc((n_vars+1), sizeof(int));
  for(i=0; i<clauses[k].original_length; ++i)
  check[abs(clauses[k].literals[i])] = clauses[k].literals[i];
  for(i=0; i<clauses[j].original_length; ++i)
  if(clauses[j].literals[i] != check[abs(clauses[j].literals[i])]){
    free(check); return NO;
  }
  free(check);
  return YES;
}

int preprocess_subsume(){
  register int n_subsumed = 0;
  register int i, j, k, c1, c2, type;
  changes_occured = FALSE;
  for(i=1; i<=n_vars; ++i){
    if(assign[i].decision != ASSIGN_NONE) continue;
    for(type=0; type<=1; ++type){
      for(j=0; j<linfo[i][type].n_occur; ++j){
        for(k=0; k<linfo[i][type].n_occur; ++k){
          if(j==k) continue;
          c1 = linfo[i][type].lit_in_clauses[j];
          c2 = linfo[i][type].lit_in_clauses[k];
          if(clauses[c1].is_satisfied ||
            clauses[c2].is_satisfied) continue;
          if(clauses[c1].original_length >=
            clauses[c2].original_length) continue;
          if(subsumable(c1, c2)){
            clauses[c2].is_satisfied = YES;
            --r_clauses;
            n_subsumed++;
            changes_occured = TRUE;
          }
        }
      }
    }
  }
}

int preprocess(){
  register int total_changes_occured, n_s = 0;
  if(n_clauses < 500) n_resolvents_threshold = n_clauses * 5;
  else if(n_clauses < 1000) n_resolvents_threshold = n_clauses * 4;
  else if(n_clauses < 1500) n_resolvents_threshold = n_clauses * 3;
  else if(n_clauses < 3000) n_resolvents_threshold = n_clauses * 2;
  else n_resolvents_threshold = n_clauses;
  while(1){
    total_changes_occured = 0;
    if(preprocess_unit_propagation()==UNSAT){
      printf("Resolvents: %d\n", resolvent_added);
      printf("Subsumed: %d\n", n_s);
      return UNSAT;
    }
    total_changes_occured += changes_occured;
    preprocess_monotone_literal_fixing();
    total_changes_occured += changes_occured;
    if(resolvent_added < n_resolvents_threshold){
      for(int i=1; i<=n_vars; ++i)
      if(assign[i].decision == ASSIGN_NONE)
      if(get_restricted_resolvent(i, 3)==UNSAT){
        printf("Resolvents: %d\n", resolvent_added);
        printf("Subsumed: %d\n", n_s);
        return UNSAT;
      }
      total_changes_occured += changes_occured;
    }
    n_s += preprocess_subsume();
    total_changes_occured += changes_occured;
    if(total_changes_occured == 0) break;
  }
  printf("Resolvents: %d\n", resolvent_added);
  printf("Subsumed: %d\n", n_s);
  return -1;
}

int add_a_clause_to_formula(int C[], int n){
  register int i;
  qsort (C, n, sizeof(int), compare);
  if(clause_present(C, n)) return FALSE;
  clauses = (clause_info *)realloc(clauses,(n_clauses+1)*sizeof(clause_info));
  clauses[n_clauses].is_satisfied = NO;
  clauses[n_clauses].current_length = n;
  clauses[n_clauses].original_length = n;
  clauses[n_clauses].binary_code = (((1<<(n-1))-1)<<1) + 1;
  clauses[n_clauses].current_ucl = 0;
  clauses[n_clauses].literals =(int *) malloc((n + 1) * sizeof(int));
  if(n>max_clause_len) max_clause_len = n;
  for(i=0; i<n; ++i){
    int p = abs(C[i]), q = C[i]>0 ? SATISFIED : SHRUNK;
    linfo[p][q].lit_in_clauses =(int *) realloc(linfo[p][q].lit_in_clauses,(linfo[p][q].n_occur+1) * sizeof(int));
    linfo[p][q].lit_in_clause_locs =(int *)realloc(linfo[p][q].lit_in_clause_locs,(linfo[p][q].n_occur+1) * sizeof(int));
    linfo[p][q].lit_in_clauses[linfo[p][q].n_occur] = n_clauses;
    linfo[p][q].lit_in_clause_locs[linfo[p][q].n_occur] = i;
    linfo[p][q].n_occur++;
    linfo[p][q].is_assigned = NO;
    clauses[n_clauses].literals[i] = C[i];
    assign[p].decision = ASSIGN_NONE;
    assign[p].type = UNASSIGNED;
  }
  if(n == 1){
    int s = abs(clauses[n_clauses].literals[0]);
    int t = clauses[n_clauses].literals[0]>0 ? SATISFIED : SHRUNK;
    linfo[s][t].antecedent_clause = n_clauses;
    if(linfo[s][(!t)].is_unit == YES){
      contradictory_unit_clauses = TRUE;
      conflicting_literal = clauses[n_clauses].literals[0];
    }
    else if(linfo[s][t].is_unit == NO){
      gucl_stack[n_gucl] = clauses[n_clauses].literals[0];
      clauses[n_clauses].current_ucl=clauses[n_clauses].literals[0];
      linfo[s][t].is_unit = YES;
      ++n_gucl;
    }
  }
  ++n_clauses;
  ++r_clauses;
  return TRUE;
}

int clause_present(int C[], int n){
  register int i, j, k, p, q;
  p = abs(C[0]); q = C[0] > 0 ? SATISFIED : SHRUNK;
  for(j=0; j<linfo[p][q].n_occur; ++j){
    if(clauses[linfo[p][q].lit_in_clauses[j]].original_length == n){
      int match_count = 0;
      for(k=0; k<n; ++k){
        if(clauses[linfo[p][q].lit_in_clauses[j]].literals[k]==C[k])
        match_count++;
        else break;
      }
      if(match_count == n) return TRUE;
    }
  }
  return FALSE;
}

inline int GetLiteralDLCS(){
  register unsigned int i, j, C;
  register unsigned int max = 0, r, s, t;
  register int u;
  for(i=1; i<=n_vars; ++i){
    if(assign[i].decision == ASSIGN_NONE){
      s = t = 0;
      for(j=0; j<linfo[i][SATISFIED].n_occur; ++j){
        C = linfo[i][SATISFIED].lit_in_clauses[j];
        s += 1-clauses[C].is_satisfied;
      }
      for(j=0; j<linfo[i][SHRUNK].n_occur; ++j){
        C = linfo[i][SHRUNK].lit_in_clauses[j];
        t += 1-clauses[C].is_satisfied;
      }
      r = s + t;
      if(r > max){
        max = r;
        if(s >= t) u = i;
        else u = -i;
      }
    }
  }
  return u;
}

int main() {
  int var,clauses;
  scanf("p cnf %d %d\n",&vars,&clauses);
  

  return 0;
}
