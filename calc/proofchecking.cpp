
#include "proofchecking.h"

#include "removelets.h"
#include "alternating.h"
#include "expander.h"
#include "projection.h"

#include "logic/pretty.h"
#include "logic/replacements.h"
#include "logic/structural.h"

size_t calc::nrsubforms( const logic::term& fm )
{
   if( !fm. option_is_kleene( ))
      throw std::logic_error( "nrsubforms: Not a Kleene operator" );

   return fm. view_kleene( ). size( );
}

const logic::term&
calc::subform( const logic::term& fm, size_t i )
{
   if( !fm. option_is_kleene( ))
      throw std::logic_error( "subform: Not a Kleene operator" ); 

   if( i >= fm. view_kleene( ). size( ))
      throw std::logic_error( "subform: index too big" ); 

   return fm. view_kleene( ). sub(i); 
}

logic::term
calc::replace( logic::term fm, size_t i, const logic::term& val )
{
   if( !fm. option_is_kleene( ))
      throw std::logic_error( "replace: Not a Kleene operator" ); 

   if( i >= fm. view_kleene( ). size( )) 
      throw std::logic_error( "replace: index too big" );

   fm. view_kleene( ). update_sub( i, val ); 
   return fm; 
}

logic::term
calc::remove( logic::term fm, size_t i )
{
   if( !fm. option_is_kleene( )) 
      throw std::logic_error( "remove: Not a Kleene operator" );

   auto kl = fm. view_kleene( );
   if( i >= kl. size( ))
      throw std::logic_error( "remove: index too big" );

   while( i + 1 < kl. size( ))
   {
      kl. update_sub( i, kl. extr_sub( i + 1 ));
      ++ i;
   }

   kl. pop_back( );
   return fm;
}


logic::term
calc::normalize( const logic::beliefstate& blfs, logic::term tm )
{
   logic::betareduction beta;
   projection proj( blfs ); 

   do 
   {
      beta. counter = 0;
      tm = outermost( beta, std::move( tm ), 0 );
   }
   while( beta. counter );
   return tm;
}

bool
calc::iscontradiction( const logic::term& fm )
{
   switch( fm. sel( ))
   {
   case logic::op_kleene_and:
      {
         auto conj = fm. view_kleene( );
         for( size_t i = 0; i != conj. size( ); ++ i )
         {
            if( iscontradiction( conj. sub(i)))
               return true;
         }
         return false; 
      }
   
   case logic::op_kleene_or:
      {
         auto disj = fm. view_kleene( );
         for( size_t i = 0; i != disj. size( ); ++ i )
         {
            if( !iscontradiction( disj. sub(i)))
               return false;
         }
         return true;
      }

   case logic::op_kleene_exists:
      {
         auto quant = fm. view_quant( ); 
         return iscontradiction( quant. body( ));
      }
   }

   return false;
}


logic::term 
calc::eval( const proofterm& prf, sequent& seq, errorstack& err )
{
   std::cout << "evaluating " << prf << "\n";

   switch( prf. sel( ))
   {
   case prf_truthconst:
      return logic::term( logic::op_kleene_and,
                             std::initializer_list< logic::term > ( ));
   case prf_exact:
      {
         auto ex = prf. view_exact( ). exact( );
         return seq. getformula( ex, err ); 
      }

   case prf_ident:
      {
         auto id = prf. view_ident( ). ident( );
         const auto& f = seq. blfs. getformulas( id ); 
         if( f. empty( ))
            throw std::logic_error( "not found" );
         if( f. size( ) > 1 )
            throw std::logic_error( "too many" ); 

         return seq. getformula( f. front( ), err );
      }

   case prf_clausify:
      {
         auto cl = prf. view_clausify( ); 
         auto fm = eval( cl. parent( ), seq, err );
         logic::context ctxt;  
         fm = removelets( seq, ctxt, fm );
         if( ctxt. size( ))
            throw std::logic_error( "context not empty" ); 

         fm = alternating( fm, logic::op_kleene_and, 2 );
         return fm;    
      }
   
   case prf_branch:
      {
         size_t nrerrors = err. size( );
         size_t seqsize = seq. size( );

         auto res = prf. view_branch( ); 
         const logic::term parent = eval( res. parent( ), seq, err );

         if( parent. sel( ) != logic::op_kleene_and )
            throw std::logic_error( "result not in ANF" );

         if( res. conj( ) >= nrsubforms( parent ))
         {
            errorstack::builder bld;
            bld << "conjunction does not have a ";
            bld << res. conj( ) << "-th conjunct";
            err. push( std::move( bld ));
            throw failure( ); 
         }        

         logic::term disj = subform( parent, res. conj( ));

         if( disj. sel( ) != logic::op_kleene_or )
         {
            err. push( "cannot branch: subformula is not a Kleene-or" );
            throw failure( );
         }

         if( res. disj( ) >= nrsubforms( disj )) 
         {
            errorstack::builder bld;
            bld << "disjunction does not have ";
            bld << res. disj( ) << "-th disjunct";
            err. push( std::move( bld ));
            throw failure( );
         }

         disj = subform( std::move( disj ), res. disj( ));
 
         // In ANF, quantifiers cannot be nested, but a while is as easy
         // to write as an if:

         {
            logic::fullsubst namesubst; 
               // We need to substitute global names in place of 
               // of the DeBruijn indices.

            while( disj. sel( ) == logic::op_kleene_exists )
            {
               auto ex = disj. view_quant( );
               for( size_t i = 0; i != ex. size( ); ++ i )
               {
                  logic::exact name = 
                     seq. assume( ex. var(i). pref, ex. var(i). tp );

                  namesubst. push( logic::term( logic::op_exact, name ));
               }

               disj = ex. body( ); 
            }

            disj = outermost( namesubst, std::move( disj ), 0 );
         }

         seq. assume( res. name( ), disj ); 
         std::cout << seq << "\n";
         std::cout << "disj = " << disj << "\n";

         auto first = eval( res. first( ), seq, err );
         if( !iscontradiction( first ))
            throw std::logic_error( "not a contradiction" );

         seq. restore( seqsize ); 
         std::cout << seq << "\n";

         auto rest = remove( subform( parent, res. conj( )), res. disj( ));
         return replace( parent, res. conj( ), rest );
      }

   case prf_expand:
      {
         auto exp = prf. view_expand( ); 
         logic::term parent = eval( exp. parent( ), seq, err ); 
         expander def( exp. ident( ), exp. occ( ), seq. blfs, err );
         std::cout << def << "\n"; 
         parent = outermost( def, std::move( parent ), 0 );
         std::cout << parent << "\n";
         parent = normalize( seq. blfs, parent );
         std::cout << "expander becomes " << def << "\n";
         return parent; 
      }

   case prf_define: 
      {
         auto def = prf. view_define( );
         size_t seqsize = seq. size( );
         
         // We need to type check the value:

         auto val = def. val( );
         size_t errsize = err. size( );
         logic::context ctxt;
         auto tp = checkandresolve( seq. blfs, err, ctxt, val );

         if( err. size( ) > errsize )
         {
            err. addheader( errsize, "during type checking of inproof definition" );
            throw failure( ); 
         } 

         if( !tp. has_value( ))
            throw std::logic_error( "should be unreachable" );

         seq. define( def. name( ), val, tp. value( ));
         auto res = eval( def. parent( ), seq, err );
         std::cout << "YOU NEED TO CHECK THAT IDENTIFIER DOES NOT OCCUR IN FORMULA";
         std::cout << "(just substitute it away)\n";
         seq. restore( errsize );
         return res;
      }

   case prf_unfinished:
      {
         errorstack::builder bld;
         bld << "--------------------------------------------------\n";
         bld << "Unfinished Proof:\n";
         bld << seq << "\n";
         auto unf = prf. view_unfinished( ); 
         for( size_t i = 0; i != unf. size( ); ++ i )
         {
            logic::context ctxt; 
            bld << i << " : "; 
            logic::pretty::print( bld, seq. blfs, ctxt, eval( unf. show(i), seq, err ));
         }
         err. push( std::move( bld ));
      }
      return logic::term( logic::op_kleene_and, {
                logic::term( logic::op_kleene_or, { } ) } );
   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check proof term" );
}



