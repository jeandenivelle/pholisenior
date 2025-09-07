
// Helper functions that make it easy to construct terms
// in code. Probably, all of these functions can go away
// when we have a good (even a temporary) parser with which 
// the test cases can be entered. 

#ifndef CALC_PROOFOPERATORS_
#define CALC_PROOFOPERATORS_

#include "proofterm.h"

namespace calc
{

#if 0
   inline term prop( const term& t ) 
      { return term( op_prop, t ); }

   inline term operator ! ( const term& t ) 
      { return term( op_not, t ); }

   inline term operator || ( const term& t1, const term& t2 ) 
      { return term( op_or, t1, t2 ); }

   inline term operator && ( const term& t1, const term& t2 )
      { return term( op_and, t1, t2 ); }

   inline term lazy_and( const term& t1, const term& t2 )
      { return term( op_lazy_and, t1, t2 ); }

   inline term implies( const term& t1, const term& t2 )
      { return term( op_implies, t1, t2 ); }

   inline term lazy_implies( const term& t1, const term& t2 )
      { return term( op_lazy_implies, t1, t2 ); }

   inline term lazy_or( const term& t1, const term& t2 )
      { return term( op_lazy_or, t1, t2 ); }

   inline term equiv( const term& t1, const term& t2 )
      { return term( op_equiv, t1, t2 ); }

   inline term operator == ( const term& t1, const term& t2 )
      { return term( op_equals, t1, t2 ); }

   inline term operator != ( const term& t1, const term& t2 )
      { return ! ( t1 == t2 ); }

   inline term forall( std::initializer_list< vartype > vars, const term& t )
      { return term( op_forall, t, vars ); }

   inline term exists( std::initializer_list< vartype > vars, const term& t )
      { return term( op_exists, t, vars ); }

   inline term apply( const term& f, std::initializer_list< term > args )
      { return term( op_apply, f, args ); }

   inline term lambda( std::initializer_list< vartype > vars, const term& t )
      { return term( op_lambda, t, vars ); }

   inline term let( const vartype& var, const term& val, const term& body )
      { return term( op_let, var, val, body ); }
#endif

   inline proofterm existselim( const proofterm& ex, size_t nr,
                                const std::string& name, const proofterm& sub )
      { return proofterm( prf_existselim, ex, nr, name, sub ); }
 
   inline proofterm conflict( const proofterm& prf )
      { return proofterm( prf_conflict, prf ); }

   inline proofterm clausify( const proofterm& prf )
      { return proofterm( prf_clausify, prf ); }

   inline proofterm 
   expand( const std::string& label, size_t nr, const proofterm& prf )
      { return proofterm( prf_expand, identifier( ) + label, nr, prf ); }

   inline proofterm show( const std::string& label, const proofterm& prf )
      { return proofterm( prf_show, label, prf ); }

}


inline calc::proofterm operator "" _assumption( const char* c, size_t len )
   { return calc::proofterm( calc::prf_ident, identifier() + c ); }

#endif 

