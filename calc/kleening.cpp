
#include "kleening.h"

logic::selector calc::kleening( logic::selector op )
{
   switch( op )
   {
   case logic::op_false:
      return logic::op_kleene_or;
   case logic::op_true:
      return logic::op_kleene_and;

   case logic::op_and:
   case logic::op_lazy_and:
      return logic::op_kleene_and;

   case logic::op_or:
      return logic::op_kleene_or; 

   case logic::op_forall:
   case logic::op_kleene_forall:
      return logic::op_kleene_forall;

   case logic::op_exists:
   case logic::op_kleene_exists: 
      return logic::op_kleene_exists;

   }
  
   std::cout << "kleening not implemented for " << op << "\n";
   throw std::runtime_error( "not implemented" ); 
}


logic::term calc::knf( const logic::term& f, polarity pol )
{
   if constexpr( false )
      std::cout << "kleening   " << f << " / " << pol << "\n";

   switch( f. sel( ))
   {
#if 0
   case logic::op_false:
   case logic::op_true:
      {
         auto s = f. sel( );
         s = kleening(s);
         s = demorgan( pol, s );
         return logic::term( s, {} );  
      }

#endif 
   case logic::op_not:
      return knf( f. view_unary( ). sub( ), -pol );

   case logic::op_implies:
   case logic::op_lazy_implies:
      {
         auto bin = f. view_binary( ); 

         auto sub1 = knf( bin. sub1( ), - pol );
         auto sub2 = knf( bin. sub2( ), pol );

         return logic::term( demorgan( pol, logic::op_kleene_or ),
                             { sub1, sub2 } );
      }

   case logic::op_and:
   case logic::op_or:
   case logic::op_lazy_and:
      {
         auto bin = f. view_binary( );
         auto sub1 = knf( bin. sub1( ), pol );
         auto sub2 = knf( bin. sub2( ), pol );

         auto kleenop = kleening( f. sel( ));
         return logic::term( demorgan( pol, kleenop ), { sub1, sub2 } );   
      } 

   case logic::op_forall:
   case logic::op_kleene_forall:
   case logic::op_exists:
   case logic::op_kleene_exists:
      {
         auto q = f. view_quant( );
         auto body = knf( q. body( ), pol );
         
         body = logic::term( demorgan( pol, kleening( f. sel( )) ), body, 
                             std::initializer_list< logic::vartype > ( ));

         // Add the quantified variables+types from the original formula:

         for( size_t i = 0; i != q. size( ); ++ i )
            body. view_quant( ). push_back( q. var(i));

         return body; 
      } 

   case logic::op_equiv:
      {
         auto eq = f. view_binary( );
        
         auto A = knf( eq. sub1( ), pol );
         auto negA = knf( eq. sub1( ), -pol );

         auto B = knf( eq. sub2( ), pol );
         auto negB = knf( eq. sub2( ), -pol );
 
         using namespace logic;

            // In case of negative polarity, we could also return
            // ( A \/ B ) /\ ( !A \/ !B ), but that seems harder
            // to handle.

         return term( demorgan( pol, op_kleene_and ),
            { term( demorgan( pol, op_kleene_or ), { negA, B } ),
              term( demorgan( pol, op_kleene_or ), { A, negB } ) } );
      }

   case logic::op_exact:
   case logic::op_debruijn:
   case logic::op_unchecked:
   case logic::op_error:
   case logic::op_equals:
   case logic::op_apply:
      return ( pol == pol_pos ) ? f : logic::term( logic::op_not, f );
   }
   std::cout << "knf " << pol << " : " << f. sel( ) << "\n";
   throw std::runtime_error( "operator not implemented" );
}
#if 0
#if 0
   {
      // Cases for # or !# : 
 
      switch( f. sel( ))
      {

      case logic::op_and:
      case logic::op_or:
      case logic::op_implies:
      case logic::op_equiv:
         {
            auto eager = f. view_binary( ); 

            auto sub1 = nnf( blfs, gen, ctxt, eager. sub1( ), pol, eq );
            auto sub2 = nnf( blfs, gen, ctxt, eager. sub2( ), pol, eq );
            return logic::term( demorgan( logic::op_kleene_and, pol ),
                                { sub1, sub2 } );
         }

      case logic::op_lazy_and:
      case logic::op_lazy_or:
      case logic::op_lazy_implies:
         {
            auto lazy = f. view_binary( ); 
            auto sub1prop = nnf( blfs, gen, ctxt, lazy. sub1( ), pol, eq );
            std::cout << sub1prop << "\n"; 
           
            polarity sub1pol = ( f. sel( ) == logic::op_lazy_and || 
                                 f. sel( ) == logic::op_lazy_implies ) ? 
                           pol_neg : pol_pos;

            if( pol == pol_negprop )
               sub1pol = negate( sub1pol );

            std::cout << sub1pol << "\n";
            auto sub1 = nnf( blfs, gen, ctxt, lazy.sub1( ), sub1pol, eq );
            std::cout << sub1 << "\n";

            auto sub2prop = nnf( blfs, gen, ctxt, lazy. sub2( ), pol, eq );
            std::cout << sub2prop << "\n";

            return logic::term( demorgan( logic::op_kleene_and, pol ),
                { sub1prop, logic::term( demorgan( logic::op_kleene_or, pol ), 
                     { sub1, sub2prop } ) } ); 
         }

      case logic::op_forall:
      case logic::op_exists:
         {
            auto q = f. view_quant( );

            size_t ss = ctxt. size( );
            for( size_t i = 0; i != q. size( ); ++ i )
               ctxt. append( q. var(i). pref, q. var(i). tp );

            auto res = nnf( blfs, gen, ctxt, q. body( ), pol, eq );

            res = logic::term( demorgan( logic::op_kleene_forall, pol ), 
                               res,
                               std::initializer_list< logic::vartype > ( ));

            // Add the quantified variables/types from the original formula:

            for( size_t i = 0; i != q. size( ); ++ i )
               res. view_quant( ). push_back( q. var(i));

            ctxt. restore( ss );

            return res; 
         }

      case logic::op_apply:
         if( pol == pol_prop )
            return logic::term( logic::op_prop, f );

         if( pol == pol_negprop )
         {
            return logic::term( logic::op_not,
                      logic::term( logic::op_prop, f ));
         }

         throw std::logic_error( "should not have been here" );
      }
      std::cout << pol << " : " << f. sel( ) << "\n";
      throw std::runtime_error( "prop not handled" );
   }
}

#endif

namespace
{
  
   void flatten_disj( std::vector< logic::term > & res,
                      logic::context& ctxt, logic::term f )
   {
      std::cout << ctxt << "\n";
      std::cout << "flatten_disj: " << f << "\n";

      if( f. sel( ) == logic::op_kleene_exists )
      {
         auto ex = f. view_quant( );
         size_t csize = ctxt. size( );
         for( size_t i = 0; i != ex. size( ); ++ i )
            ctxt. append( ex. var(i). pref, ex. var(i). tp );  
         flatten_disj( res, ctxt, ex. body( ));
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
   }
                    

   void flatten_conj( std::vector< logic::term > & res,
                      logic::context& ctxt, logic::term f )
   {
      std::cout << ctxt << "\n";
      std::cout << "flatten_conj: " << f << "\n";

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

      res. push_back( std::move(f) );
   }
   
}


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



logic::term reso::atom( identifier pred, const logic::type& preddtype )
{
   logic::term res = logic::term( logic::op_unchecked, pred );
   res = logic::term( logic::op_apply, res, 
                      std::initializer_list< logic::term > ( ));
  
   auto f = preddtype. view_func( );
   auto ap = res. view_apply( );

   for( size_t v = f. size( ); v -- ; )
      ap. push_back( logic::term( logic::op_debruijn, v ));

   return res;
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

