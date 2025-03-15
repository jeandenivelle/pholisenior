
#include "alternating.h"

bool calc::isliteral( const logic::term& f )
{
   switch( f. sel( ))
   {
   case logic::op_exact:
   case logic::op_debruijn:
   case logic::op_unchecked:
   case logic::op_error:
   case logic::op_not: 
   case logic::op_prop:
   case logic::op_equals:
   case logic::op_apply:
      return true;
   default:
      return false;
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
   std::cout << ctxt << "\n";
   std::cout << "   flatten_disj: " << f << "\n";

   if( f. sel( ) == logic::op_kleene_or )
   {
      auto kl = f. view_kleene( );
      for( size_t i = 0; i != kl. size( ); ++ i )
         flatten_disj( ctxt, kl. sub(i), into );
      return;
   }

    
#if 0
      std::cout << ctxt << "\n";
      std::cout << "flatten_disj: " << f << "\n";

      if( f. sel( ) == logic::op_kleene_exists )
      {
         auto ex = f. view_quant( );
         size_t csize = ctxt. size( );
         for( size_t i = 0; i != ex. size( ); ++ i )
            ctxt. append( ex. var(i). pref, ex. var(i). tp );  
         flatten_disj( into, ctxt, ex. body( ));
         ctxt. restore( csize );  
         return; 
      }

      if( f. sel( ) == logic::op_kleene_or )
      {
         auto kl = f. view_kleene( );
         for( size_t i = 0; i != kl. size( ); ++ i )
            flatten_disj( res, ctxt, kl. sub(i));
         return;
      }

      f = reso::flatten( std::move(f)); 

      if( ctxt. size( ) > 0 )
      {
         f = logic::term( logic::op_kleene_exists, f, 
                          std::initializer_list< logic::vartype > ( ));
         size_t ind = ctxt. size( );
         while( ind )
         {
            -- ind;
            f. view_quant( ). push_back( logic::vartype( ctxt. getname( ind ),
                                                 ctxt. gettype( ind ))); 
         } 
      }

      res. push_back( std::move(f) );
#endif 
   into. push_back( alt_conj( std::move(f) ));
}

logic::term calc::alt_conj( logic::term f )
{
   std::cout << "alt_conj: " << f << "\n";

   if( isliteral(f))
      throw std::runtime_error( "stop it" );

   std::vector< logic::term > conj;
   logic::context ctxt;
   flatten_conj( ctxt, f, conj );

   return logic::term( logic::op_kleene_and, conj. begin( ), conj. end( ));
}


void
calc::flatten_conj( logic::context& ctxt, const logic::term& f,
                    std::vector< logic::term > & into )
{
   std::cout << ctxt << "\n";
   std::cout << "flatten conj: " << f << "\n";

   if( f. sel( ) == logic::op_kleene_and )
   {
      auto kl = f. view_kleene( );
      for( size_t i = 0; i != kl. size( ); ++ i )
         flatten_conj( ctxt, kl. sub(i), into );
      return;
   }

#if 0                    
      if( f. sel( ) == logic::op_kleene_forall )
      {
         auto ex = f. view_quant( );
         size_t csize = ctxt. size( );
         for( size_t i = 0; i != ex. size( ); ++ i )
            ctxt. append( ex. var(i). pref, ex. var(i). tp );
         flatten_conj( res, ctxt, ex. body( ));
         ctxt. restore( csize );
         return;  
      }

      if( f. sel( ) == logic::op_kleene_and )
      {
         auto kl = f. view_kleene( );
         for( size_t i = 0; i != kl. size( ); ++ i ) 
            flatten_conj( res, ctxt, kl. sub(i));
         return; 
      }

      f = reso::flatten( std::move(f));

      if( ctxt. size( ) > 0 )
      {
         f = logic::term( logic::op_kleene_forall, f,
                          std::initializer_list< logic::vartype > ( ));
         size_t ind = ctxt. size( );
         while( ind )
         {
            -- ind;
            f. view_quant( ). push_back( logic::vartype( ctxt. getname( ind ),
                                                 ctxt. gettype( ind )));
         }
      }

#endif
   if( ctxt. size( ))
   {
      auto all = logic::term( logic::op_kleene_forall, f, 
                              std::initializer_list< logic::vartype > ( ));
      auto q = all. view_quant( ); 
      throw std::runtime_error( "finishthis" );
   }
   else
      into. push_back( std::move(f) );
}
   

#if 0

logic::term
reso::flatten( logic::term f )
{
   switch( f. sel( ))
   {
   case logic::op_kleene_or:
   case logic::op_kleene_exists:
      {
         std::vector< logic::term > disj;
         logic::context ctxt;
         flatten_disj( disj, ctxt, f );
 
         // If the resulting disjunction contains only
         // one element, we don't build it.
         // Not sure if this should be done.

         if( disj. size( ) == 1 )
            return disj. front( );
         else
            return logic::term( logic::op_kleene_or, 
                                disj. begin( ), disj. end( )); 
      }   

   case logic::op_kleene_and:
   case logic::op_kleene_forall:
      {
         std::vector< logic::term > conj;
         logic::context ctxt;
         flatten_conj( conj, ctxt, f );
         if( conj. size( ) == 1 )
            return conj. front( );
         else
            return logic::term( logic::op_kleene_and,
                                conj. begin( ), conj. end( )); 
      }

   case logic::op_apply:
   case logic::op_equals:
   case logic::op_not:
      return f;
   }

   throw std::runtime_error( "cannot handle" ); 
}


logic::term reso::forall( const logic::type& preddtype, 
                          logic::term form )
{
   form = logic::term( logic::op_kleene_forall, form,
                      std::initializer_list< logic::vartype > ( ));
 
   auto f = preddtype. view_func( );
   auto q = form. view_quant( );

   for( size_t i = 0; i != f. size( ); ++ i )
      q. push_back( { "xx", f. arg(i) } );
  
   return form;
}


logic::term
reso::define_subform( logic::beliefstate& blfs, 
                      namegenerators& gen,
                      logic::context& ctxt, logic::term ff,  
                      logic::selector defop )
{
   // Create the type of pred:

   auto T = logic::type( logic::type_truthval ); 
   
   auto predtype = logic::type( logic::type_func, T, {} );

   for( auto it = freevars. end( ); it != freevars. begin( ); )
   {
      -- it; 
      predtype. view_func( ). push_back( 
                                  ctxt. gettype( it -> first ));
   }

   std::cout << predtype << "\n"; 

   // Add the declaration of pred:

   blfs. append( logic::belief( logic::bel_decl, pred, predtype ));

   // In ff, we need to normalize the variables to #s, ... ,#0 :

   logic::sparse_subst norm;

   {
      auto it = freevars. begin( );
      size_t var = 0;
      while( it != freevars. end( ))
      {
         norm. assign( it -> first, logic::term( logic::op_debruijn, var )); 
         ++ it; ++ var;
      }
   }

   std::cout << "norm = " << norm << "\n";

   bool change = false; 
   ff = topdown( norm, std::move( ff ), 0, change );

   std::cout << "normalized ff = " << ff << "\n";

   auto predatom = atom( pred, predtype );
   auto prop = forall( predtype, logic::term( logic::op_prop, predatom ));

   blfs. append( logic::belief( logic::bel_form, 
                    freshident( blfs, gen. predisprop ), prop, { } ));

   auto def = logic::term( logic::op_error );

   switch( defop )
   {
   
   case logic::op_equiv:
      {
         def = forall( predtype, 
                  logic::term( logic::op_equiv, predatom, ff ));
         break;
      }

   default:
      std::cout << "defop = " << defop << "\n";
      throw std::runtime_error( "define subform: cannot handle" );
   }

   std::cout << "def = " << def << "\n";

   blfs. append( logic::belief( logic::bel_form, 
                                freshident( blfs, gen. preddef ), def, { } ));

   return predatom;
}

#endif

