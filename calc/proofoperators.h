
// Helper functions that make it easy to construct terms
// in code. Probably, all of these functions can go away
// when we have a good (even a temporary) parser with which 
// the test cases can be entered. 

#ifndef CALC_PROOFOPERATORS_
#define CALC_PROOFOPERATORS_

#include "proofterm.h"

namespace calc
{

   inline proofterm orelim( const proofterm& disj, size_t nr,
                            const std::string& name1, const proofterm& sub1,
                            const std::string& name2, const proofterm& sub2 )
   {
      return proofterm( prf_orelim, disj, nr, 
                        {{ name1, sub1 }, { name2, sub2 }} );
   }
 
   inline proofterm existselim( const proofterm& ex, size_t nr,
                                const std::string& name, const proofterm& sub )
      { return proofterm( prf_existselim, ex, nr, name, sub ); }
 
   inline proofterm simplify( const proofterm& prf )
      { return proofterm( prf_simplify, prf ); }

   inline proofterm clausify( const proofterm& prf )
      { return proofterm( prf_clausify, prf ); }

   inline proofterm 
   expand( const std::string& label, size_t nr, const proofterm& prf )
      { return proofterm( prf_expand, identifier( ) + label, nr, prf ); }

   inline proofterm andintro( std::initializer_list< proofterm > sub ) 
      { return proofterm( prf_andintro, sub ); } 

   inline proofterm select( std::initializer_list< size_t > nr,
                            const proofterm& prf )
   {
      return proofterm( prf_select, prf, nr ); 
   }
      
   inline proofterm show( const std::string& label, const proofterm& prf )
      { return proofterm( prf_show, label, prf ); }

}

inline calc::proofterm operator "" _assumption( const char* c, size_t len )
   { return calc::proofterm( calc::prf_ident, identifier() + c ); }

#endif 

