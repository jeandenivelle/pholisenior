
#include "alternating.h"

bool calc::isatom( const logic::term& f )
{
   switch( f. sel( ))
   {
   case logic::op_exact:
   case logic::op_debruijn:
   case logic::op_unchecked:
   case logic::op_equals:
   case logic::op_apply:
      return true;
   default:
      return false;
   }
}

bool calc::isliteral( const logic::term& f )
{
   if( f. sel( ) == logic::op_not || f. sel( ) == logic::op_prop )
      return isliteral( f. view_unary( ). sub( ));
   else
      return isatom(f); 
}

logic::term
calc::quantify( logic::selector op, const logic::context& ctxt,
                const logic::term& body )
{
   if( ctxt. size( ) == 0 )
      return body;
   else
   {
      std::cout << ctxt << "\n";
      auto res = logic::term( op, body, 
                              std::initializer_list< logic::vartype > ( ));
      auto q = res. view_quant( );

      // We need to do in reverse order, because context looks back: 

      for( size_t i = ctxt. size( ); i -- ; )
         q. push_back( logic::vartype( ctxt. getname(i), ctxt. gettype(i) ));
      std::cout << "res = " << res << "\n";
      return res;
   }
}

logic::term calc::alt_disj( logic::term f )
{
   std::cout << "alt disj: " << f << "\n";

   std::vector< logic::term > disj;
   logic::context ctxt; 
   flatten_disj( ctxt, f, disj );
   return logic::term( logic::op_kleene_or, disj. begin( ), disj. end( ));
}


void 
calc::flatten_disj( logic::context& ctxt, const logic::term& f, 
                    std::vector< logic::term > & into )
{
   if( f. sel( ) == logic::op_kleene_or )
   {
      auto kl = f. view_kleene( );
      for( size_t i = 0; i != kl. size( ); ++ i )
         flatten_disj( ctxt, kl. sub(i), into );
      return;
   }

   if( f. sel( ) == logic::op_kleene_exists )
   {
      auto ex = f. view_quant( );
      size_t csize = ctxt. size( );
      for( size_t i = 0; i != ex. size( ); ++ i )
         ctxt. append( ex. var(i). pref, ex. var(i). tp );  
      flatten_disj( ctxt, ex. body( ), into );
      ctxt. restore( csize );  
      return; 
   }

   if( isliteral(f))
   {
      into. push_back( quantify( logic::op_kleene_exists, ctxt, f ));
      return;
   }

   if( f. sel( ) == logic::op_kleene_forall ||
       f. sel( ) == logic::op_kleene_and )
   {
      into. push_back( quantify( logic::op_kleene_exists, ctxt,
                                 alt_conj(f)));
      return;
   }

   throw std::runtime_error( "alt_conj: formula not in KNF" );
}

logic::term calc::alt_conj( logic::term f )
{
   std::cout << "alt conj: " << f << "\n";

   std::vector< logic::term > conj;
   logic::context ctxt;
   flatten_conj( ctxt, f, conj );

   return logic::term( logic::op_kleene_and, conj. begin( ), conj. end( ));
}


void
calc::flatten_conj( logic::context& ctxt, const logic::term& f,
                    std::vector< logic::term > & into )
{
   if( f. sel( ) == logic::op_kleene_and )
   {
      auto kl = f. view_kleene( );
      for( size_t i = 0; i != kl. size( ); ++ i )
         flatten_conj( ctxt, kl. sub(i), into );
      return;
   }

   if( f. sel( ) == logic::op_kleene_forall )
   {
      auto all = f. view_quant( );
      size_t csize = ctxt. size( );
      for( size_t i = 0; i != all. size( ); ++ i )
         ctxt. append( all. var(i). pref, all. var(i). tp );
      flatten_conj( ctxt, all. body( ), into );
      ctxt. restore( csize );
      return;  
   }

   if( isliteral(f))
   {
      into. push_back( quantify( logic::op_kleene_forall, ctxt, f ));
      return;
   }

   if( f. sel( ) == logic::op_kleene_exists || 
       f. sel( ) == logic::op_kleene_or )
   {
      into. push_back( quantify( logic::op_kleene_forall, ctxt,
                                 alt_disj(f))); 
      return;
   }

   throw std::runtime_error( "alt_conj: formula not in KNF" );
}


