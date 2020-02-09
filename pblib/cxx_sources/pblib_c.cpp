#include <iterator>
#include <string.h>
#include "pblib_c.h"


using namespace std;
using namespace PBLib;

PBLib::WeightedLit* new_WeightedLit(int32_t lit, int64_t weight) {
  return new PBLib::WeightedLit(lit, weight);
}

C_Encoder* new_C_Encoder(
    PB_ENCODER::PB2CNF_PB_Encoder pb_encoder,
    AMK_ENCODER::PB2CNF_AMK_Encoder amk_encoder,
    AMO_ENCODER::PB2CNF_AMO_Encoder amo_encoder,
    BIMANDER_M_IS::BIMANDER_M_IS bimander_m_is,
    int bimander_m,
    int k_product_minimum_lit_count_for_splitting,
    int k_product_k,
    int commander_encoding_k,
    int64_t MAX_CLAUSES_PER_CONSTRAINT,
    bool use_formula_cache,
    bool print_used_encodings,
    bool check_for_dup_literals,
    bool use_gac_binary_merge,
    bool binary_merge_no_support_for_single_bits,
    bool use_recursive_bdd_test,
    bool use_real_robdds,
    bool use_watch_dog_encoding_in_binary_merger,
    bool just_approximate,
    int64_t approximate_max_value,
    int32_t first_free_variable
) {
    PBConfig config = make_shared<PBConfigClass>();
    config->pb_encoder = pb_encoder;
    config->amk_encoder = amk_encoder;
    config->amo_encoder = amo_encoder;
    config->bimander_m_is = bimander_m_is;
    config->bimander_m = bimander_m;
    config->k_product_minimum_lit_count_for_splitting = k_product_minimum_lit_count_for_splitting;
    config->k_product_k = k_product_k;
    config->commander_encoding_k = commander_encoding_k;
    config->MAX_CLAUSES_PER_CONSTRAINT = MAX_CLAUSES_PER_CONSTRAINT;
    config->use_formula_cache = use_formula_cache;
    config->print_used_encodings = print_used_encodings;
    config->check_for_dup_literals = check_for_dup_literals;
    config->use_gac_binary_merge = use_gac_binary_merge;
    config->binary_merge_no_support_for_single_bits = binary_merge_no_support_for_single_bits;
    config->use_recursive_bdd_test = use_recursive_bdd_test;
    config->use_real_robdds = use_real_robdds;
    config->use_watch_dog_encoding_in_binary_merger = use_watch_dog_encoding_in_binary_merger;
    config->just_approximate = just_approximate;
    config->approximate_max_value = approximate_max_value;

    VectorClauseDatabase* formula = new VectorClauseDatabase(config);

    PB2CNF* pb2cnf = new PB2CNF(config);
    AuxVarManager* auxvars = new AuxVarManager(first_free_variable);
    
    C_Encoder* e  = (C_Encoder*)malloc(sizeof(C_Encoder));
    e->constraint = new vector<IncPBConstraint*>;
    e->clauseDb   = formula;
    e->auxManager = auxvars;
    e->encoder    = pb2cnf;
    return e;
}

const IncPBConstraint* new_c_Constraint( C_Encoder* e, PBLib::WeightedLit** literals, 
                                         size_t numLiterals, PBLib::Comparator comp, 
                                         int64_t lowerBound, int64_t upperBound) {

    PB2CNF* pb2cnf = e->encoder;
    VectorClauseDatabase* formula = e->clauseDb;
    AuxVarManager* auxManager = e->auxManager;

    vector<PBLib::WeightedLit>* literals_v = new vector<PBLib::WeightedLit>();
    for(int i = 0; i < numLiterals; i++) {
        PBLib::WeightedLit* lit = literals[i];
        literals_v->push_back(*lit);
    }

    IncPBConstraint* constraint;
    if(comp == PBLib::BOTH)
        constraint = new IncPBConstraint(*literals_v, comp, upperBound, lowerBound);
    else if(comp == PBLib::LEQ)
        constraint = new IncPBConstraint(*literals_v, comp, upperBound);
    else
        constraint = new IncPBConstraint(*literals_v, comp, lowerBound);

    pb2cnf->encodeIncInital(*constraint, *formula, *auxManager);
    e->constraint->push_back(constraint);
    return constraint;
}

void free_C_Encoder(C_Encoder* e) {
    delete e->constraint;
    delete e->clauseDb;
    delete e->auxManager;
    delete e->encoder;
    delete e;
}

void free_C_Clauses(C_Cnf* cnf) {
    delete cnf->dimacs;
    delete cnf;
}

void c_encodeNewGeq(C_Encoder* e, IncPBConstraint* constraint, int64_t newGeq) {
    constraint->encodeNewGeq(newGeq, *(e->clauseDb), *(e->auxManager));
}
void c_encodeNewLeq(C_Encoder* e, IncPBConstraint* constraint, int64_t newLeq) {
    constraint->encodeNewLeq(newLeq, *(e->clauseDb), *(e->auxManager));
}

void c_addConditional(IncPBConstraint* constraint, int32_t cond) {
    constraint->addConditional(cond);
}

void c_clearConditional(IncPBConstraint* constraint) {
    constraint->clearConditionals();
}

void c_clearDB(C_Encoder* e) {
    e->clauseDb->clearDatabase();
}

const C_Cnf* c_getClauses(C_Encoder* e) {
    VectorClauseDatabase* formula = e->clauseDb;
    vector<vector<int32_t>> clauses_v = formula->getClauses();
    // create
    C_Cnf* clauses = (C_Cnf*) malloc(sizeof(C_Cnf));
    clauses->size = clauses_v.size(); 
    for( vector<int32_t> c : clauses_v ) {
        clauses->size += c.size();
    }
    clauses->dimacs = (int32_t*) malloc(sizeof(int32_t) * clauses->size);

    // fill literals
    int32_t* pos = clauses->dimacs;
    for( vector<int32_t> c : clauses_v ){
        memcpy(pos, c.data(), sizeof(int32_t) * c.size() );
        pos[c.size()] = 0;
        pos += c.size() + 1;
    }
    clauses->size--; // Dont use the last 0.

    return clauses;
}
