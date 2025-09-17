
#include "proofchecking.h"

#include "logic/pretty.h"
#include "logic/replacements.h"
#include "logic/structural.h"
#include "logic/cmp.h"
#include "logic/inspections.h"

#include "formulaset.h"
#include "expander.h"

#include "printing.h"

bool calc::iscontradiction( const logic::term& fm )
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


bool 
calc::inconflict( bool neg1, const logic::term& tm1,
                  bool neg2, const logic::term& tm2 )
{
   std::cout << neg1 << "  " << tm1 << "   " << neg2 << "  " << tm2 << "\n";

   if( neg1 && !neg2 && logic::equal( tm1, tm2 ))
      return true;

   if( !neg1 && neg2 && logic::equal( tm1, tm2 ))
      return true;

   if( neg1 && tm1. sel( ) == logic::op_prop &&
       logic::equal( tm1. view_unary( ). sub( ), tm2 ))
   {
      return true;
   }
      
   if( neg2 && tm2. sel( ) == logic::op_prop &&
       logic::equal( tm1, tm2. view_unary( ). sub( )) )
   {
      return true;
   }

   return false;
}

bool 
calc::inconflict( const logic::term& tm1, const logic::term& tm2 )
{
   // This is probably a point where one would like to have matching.
   // We try to bring some order in the chaos by separating out
   // negation.

   if( tm1. sel( ) == logic::op_not )
   {
      if( tm2. sel( ) == logic::op_not )
      {
         return inconflict( true, tm1. view_unary( ). sub( ),
                            true, tm2. view_unary( ). sub( )); 
      }
      else
         return inconflict( true, tm1. view_unary( ). sub( ), false, tm2 ); 
   }
   else
   {
      if( tm2. sel( ) == logic::op_not )
         return inconflict( false, tm1, true, tm2. view_unary( ). sub( ) );
      else
         return inconflict( false, tm1, false, tm2 );
   }
}

bool 
calc::inconflict( std::vector< logic::term > & checked,
                  std::vector< logic::term > & unchecked )
{
restart: 
   if( unchecked. empty( ))
      return false;

   auto picked = std::move( unchecked. back( ));
   unchecked. pop_back( ); 

   std::cout << "picked: " << picked << "\n";

   if( picked. sel( ) == logic::op_not )
   {
      const auto& sub = picked. view_unary( ). sub( );
      if( sub. sel( ) == logic::op_equals )
      {
         auto eq = sub. view_binary( );
         if( logic::equal( eq. sub1( ), eq. sub2( )) )
            return true;  
      }
   }

   if( picked. sel( ) == logic::op_kleene_and )
   {
      auto kl = picked. view_kleene( );
      for( size_t i = 0; i != kl. size( ); ++ i )
         unchecked. push_back( kl. extr_sub(i) );
      goto restart; 
   }

   if( picked. sel( ) == logic::op_kleene_or )
   {
      auto kl = picked. view_kleene( );
      if( kl. size( ) == 0 )
         return true;
      if( kl. size( ) == 1 )
      {
         unchecked. push_back( kl. extr_sub(0));
         goto restart;
      }
      goto restart;
   }

   for( const auto& ch : checked )
   {
      if( inconflict( ch, picked ))
         return true;
   }

   checked. push_back( std::move( picked ));
   goto restart;
}

std::optional< logic::term >
calc::deduce( const proofterm& prf, sequent& seq, errorstack& err )
{
   switch( prf. sel( ))
   {

   case prf_ident:
      {
         auto id = prf. view_ident( ). ident( );
         const auto& f = seq. blfs. getformulas( id ); 
         if( f. empty( ))
         {
            errorstack::builder bld;
            bld << "unknown identifier " << id << " was used in a proof\n";
            bld << seq << "\n";
            err. push( std::move( bld ));
            return { };
         }

         if( f. size( ) > 1 )
         {
            errorstack::builder bld; 
            bld << "ambiguous identifier " << id << " was used in a proof\n";
            bld << seq << "\n";
            err. push( std::move( bld ));
            return { };
         }

         return seq. getformula( f. front( ), err );
      }

   case prf_clausify:
      {
         auto cl = prf. view_clausify( ); 
         auto fm = deduce( cl. parent( ), seq, err );
         if( !fm. has_value( ))
            return { };

         auto res = optform( std::move( fm ), "clausify", seq, err );
         res. make_anf2( );
         return res. value( );
      }

   case prf_orelim:
      {
         auto elim = prf. view_orelim( ); 
         auto conj = deduce( elim. parent( ), seq, err );

         if( !conj. has_value( ))
            return conj;

         auto disj = optform( std::move( conj ), "or-elim", seq, err );
         disj. musthave( logic::op_kleene_and );
         disj. replacebysub( elim. nror( ));
         disj. musthave( logic::op_kleene_or );
         disj. aritymustbe( elim. size( ));
         if( !disj )
            return { };
 
         auto kl = disj. value( ). view_kleene( );
         size_t seqsize = seq. size( );
         bool success = true;
         formulaset intro;

         for( size_t i = 0; i != kl. size( ); ++ i )
         {
            {
               auto sub = optform( kl. sub(i), "or-elim", seq, err );
               sub. make_anf2( );
               seq. assume( elim. name(i), sub. value( ));
            }

            auto res = optform( deduce( elim. branch(i), seq, err ),
                                "option in or-elim", seq, err );
              
            res. musthave( logic::op_kleene_and );
            res. getuniquesub( );
            res. musthave( logic::op_kleene_or );

            if( !res )
               success = false; 
            else
            {
               auto disj = res. value( ). view_kleene( );
               for( size_t i = 0; i != disj. size( ); ++ i )
                  intro. insert( disj. sub(i));  
            }

            seq. restore( seqsize );
         }

         if( !success )
            return { };

         return logic::term( logic::op_kleene_and,
            { logic::term( logic::op_kleene_or, 
                           intro. begin( ), intro. end( )) } );
      }

   case prf_expand:
      {
         auto exp = prf. view_expand( ); 

         auto parent = deduce( exp. parent( ), seq, err ); 
         if( !parent. has_value( ))
            return { };

         auto nm = optform( std::move( parent ), "expand", seq, err );

         expander def( exp. ident( ), exp. occ( ), seq. blfs, err );
            // We are using unchecked identifier exp. ident( ).
            // The expander will look only at exact overloads. 
            // This guarantees type safety.

         std::cout << def << "\n"; 

         nm. rewr_outermost( def ); 
         nm. normalize( );
         // nm. make_anf2( );
         std::cout << "expand returns " << nm << "\n";
         return nm. value( );
      }

   case prf_define: 
      {
         auto def = prf. view_define( );

         // We first need to typecheck the value:

         auto val = def. val( );
         size_t errsize = err. size( );
         logic::context ctxt;
         auto tp = checkandresolve( seq. blfs, err, ctxt, val );

         if( err. size( ) > errsize )
         {
            err. addheader( errsize, "during type checking of inproof definition" );
            throw std::logic_error( "do something" );
         } 

         if( !tp. has_value( ))
            throw std::logic_error( "should be unreachable" );

         size_t seqsize = seq. size( );
         seq. define( def. name( ), val, tp. value( ));
         
         auto res = deduce( def. parent( ), seq, err );
         if( !res. has_value( ))
         {
            seq. restore( seqsize ); 
            return res; 
         }

         logic::rewritesystem rewr;
         rewr. append( 
            logic::term( logic::op_exact, seq. getexactname( seqsize )), 
            val );

         res. value( ) = outermost( rewr, std::move( res. value( )), 0 );
         seq. restore( seqsize );
         return res;
      }

   case prf_cut:
      {
         auto cut = prf. view_cut( );

         // We evaluate the first parent: 

         auto first = deduce( cut. first( ), seq, err );
         if( !first. has_value( ))
            return { };

         size_t seqsize = seq. size( );
         seq. assume( cut. name( ), first. value( ));

         auto res = deduce( cut. second( ), seq, err );
         seq. restore( seqsize );
         return res;
      }
   
   case prf_existselim:
      {
         auto elim = prf. view_existselim( );
         auto conj = deduce( elim. parent( ), seq, err );

         if( !conj. has_value( ))
            return conj;

         auto exists = optform( conj, "exists-elim", seq, err );
         exists. musthave( logic::op_kleene_and ); 
         exists. replacebysub( elim. nrexists( ));
         exists. musthave( logic::op_kleene_or );
         exists. getuniquesub( );
         exists. musthave( logic::op_kleene_exists );

         if( !exists )
            return { };

         // At this point, we are sure that existselim can be applied:

         size_t seqsize = seq. size( );

         std::vector< logic::vartype > assumptions;
         std::vector< logic::exact > exactnames;
            // The names that seq will give to the assumptions.
            // Note that the sequent data structure is rotten.

         while( exists. value( ). sel( ) == logic::op_kleene_exists )
         {
            auto ex = exists. value( ). view_quant( );
            for( size_t i = 0; i != ex. size( ); ++ i )
               assumptions. push_back( ex. var(i));

            exists. value( ) = ex. body( );
         }

         for( const auto& a : assumptions ) 
         {
            logic::exact name = seq. assume( a.pref, a.tp );
            exactnames. push_back( name );
         }

         {
            logic::fullsubst namesubst;
               // We need to substitute global names in place of
               // of the DeBruijn indices.

            for( const auto& e : exactnames )
               namesubst. push( logic::term( logic::op_exact, e ));

            exists. rewr_outermost( namesubst );
         }

         exists. make_anf2( );

         seq. assume( elim. name( ), exists. value( ));

         auto res = optform( deduce( elim. intro( ), seq, err ),
                             "subresult of exists-elim", seq, err );

         // We require that the result is a singleton conjunction:

         res. musthave( logic::op_kleene_and );
         res. getuniquesub( );
         res. musthave( logic::op_kleene_or );
         if( !res )
         {
            seq. restore( seqsize ); 
            return { };
         }

         logic::exactcounter eigenvars( false );
         for( size_t i = seqsize; i + 1 < seq. size( ); ++ i )
            eigenvars. addtodomain( seq. getexactname(i));

         count( eigenvars, res. value( ), 0 );

         logic::introsubst intro;

         std::vector< logic::vartype > usedassumptions;
            // The ones that are used in the result. They need
            // to be assumed.
         
         for( size_t i = 0; i != exactnames. size( ); ++ i )
         {
            if( eigenvars. at( exactnames[i] ))
            {
               intro. bind( exactnames[i] ); 
               usedassumptions. push_back( assumptions[i] );
            }
         }
         seq. restore( seqsize );
         
         // If no eigenvariable occurs in res, we can return res
         // unchanged:

         if( intro. size( ))
         {
            res. rewr_outermost( intro );
            res. quantify( usedassumptions ); 
         }
         return logic::term( logic::op_kleene_and, { res. value( ) } );
      }

   case prf_forallintro:
      {
         auto intro = prf. view_forallintro( );

         std::vector< logic::exact > exactnames;
            // The names that seq will give to the assumptions.
            // We need them, so that we can subtitute them away later.

         auto seqsize = seq. size( );
         for( size_t i = 0; i != intro. size( ); ++ i )
         {
            logic::exact name = 
               seq. assume( intro.var(i).pref, intro.var(i).tp );

            exactnames. push_back( name );
         }
 
         auto res = optform( deduce( intro. parent( ), seq, err ), 
                             "forall-intro", seq, err );

         if( !res )
            return { };

         res. musthave( logic::op_kleene_and );
        
         logic::introsubst subst;
         for( const auto& e : exactnames )
            subst. bind(e);

         res. rewr_outermost( subst );

         std::vector< logic::vartype > vars; 
         for( size_t i = 0; i != intro. size( ); ++ i ) 
            vars. push_back( intro. var(i));
 
         res. quantify( vars );
         seq. restore( seqsize );

         return res. value( ); 
      }

   case prf_forallelim:
      {
         auto elim = prf. view_forallelim( );
         auto anf = deduce( elim. parent( ), seq, err );
         if( !anf. has_value( ))
            return anf;

         auto forall = optform( std::move( anf ), "forall-elim", seq, err );
         forall. musthave( logic::op_kleene_and );
         forall. replacebysub( elim. nrforall( ));
         forall. musthave( logic::op_kleene_forall );
         forall. nrvarsmustbe( elim. size( )); 

         if( !forall ) return { };

         size_t errstart = err. size( );
         logic::fullsubst subst;

         auto q = forall. value( ). view_quant( ); 
         for( size_t i = 0; i != elim. size( ); ++ i )
         {
            logic::context ctxt;
            auto tm = elim. value(i);
            auto tp = checkandresolve( seq. blfs, err, ctxt, tm );

            if( tp. has_value( )) 
            {
               if( logic::equal( tp. value( ), q. var(i). tp ))
               {
                  subst. push( std::move( tm ));
               }
               else
               {
                  auto bld = errorstack::builder( ); 
                  bld << "true type of instance ";
                  printing::pretty( bld, seq, tm );
                  bld << " is wrong\n"; 
                  bld << "It is "; 
                  printing::pretty( bld, seq, tp. value( ));
                  bld << ", but must be ";
                  printing::pretty( bld, seq, q. var(i). tp ); 
                  err. push( std::move( bld ));
               }
            }
         }
        
         if( subst. size( ) < elim. size( ))
         {
            auto header = printing::makeheader( seq, "forall-elim" );
            err. addheader( errstart, std::move( header )); 
            return { };
         } 
         auto res = outermost( subst, std::move( q. body( )), 0 ); 
         res = logic::term( logic::op_kleene_and, { res } );
         return res; 
      }

   case prf_eqrepl:
      {
         auto eqrepl = prf. view_eqrepl( );
         auto anf = optform( deduce( eqrepl. parent( ), seq, err ),
                             "eq-repl", seq, err );

         anf. musthave( logic::op_kleene_and );

         if( !anf ) 
            return { };   // Not a Kleene-and, bye bye! 

         auto errsize = err. size( );

         logic::rewritesystem sys;
     
         auto kl = anf. value( ). view_kleene( );
         std::vector< bool > equalities;
         for( size_t i = 0; i != kl. size( ); ++ i )
            equalities. push_back( false );  

         for( size_t i = 0; i != eqrepl. size( ); ++ i )
         {
            if( eqrepl. eqnr(i) >= kl. size( ))
            {
               auto bld = errorstack::builder( );
               bld << "selected equality " << eqrepl. eqnr(i);
               bld << " >= " << kl. size( );
               err. push( std::move( bld ));
            }
            else
            {
               auto disj = kl. sub( eqrepl. eqnr(i) );
               if( disj. sel( ) != logic::op_kleene_or ||
                   disj. view_kleene( ). size( ) != 1 )
               {
                  auto bld = errorstack::builder( );
                  bld << "selected equality " << eqrepl. eqnr(i);
                  bld << " is not an equality";
                  err. push( std::move( bld ));
               } 
               else
               {
                  auto eq = disj. view_kleene( ). sub(0); 
                  if( eq. sel( ) != logic::op_equals ) 
                  {
                     auto bld = errorstack::builder( );
                     bld << "selected equality " << eqrepl. eqnr(i);
                     bld << " is not an equality"; 
                     err. push( std::move( bld ));
                  } 
                  else
                  {
                     auto bin = eq. view_binary( );
                     if( eqrepl. leftright(i))
                        sys. append( bin. sub1( ), bin. sub2( ));
                     else
                        sys. append( bin. sub2( ), bin. sub1( )); 

                     equalities[ eqrepl. eqnr(i) ] = true;
                  }
               }
            }
         }

         std::cout << sys << "\n";
         for( auto b : equalities )
            std::cout << b << " ";
         std::cout << "\n";
         for( size_t i = 0; i != kl. size( ); ++ i )
         {
            if( !equalities[i] )
            {
               for( size_t nr = 0; nr != eqrepl. times( ); ++ nr )
               {
                  kl. update_sub( i, outermost( sys, kl. extr_sub(i), 0 )); 
               }
            } 
         }

         return anf. value( );
      }

   case prf_andintro:
      {
         auto intro = prf. view_andintro( ); 

         formulaset result;

         for( size_t i = 0; i != intro. size( ); ++ i )
         {
            auto fm = deduce( intro. parent(i), seq, err );

            // There is no point in continuing I think:

            if( !fm. has_value( ))
               return fm; 

            auto conj = optform( std::move( fm ), "andintro", seq, err );
            conj. musthave( logic::op_kleene_and );
            if( !conj )
               return { };

            auto kl = conj. value( ). view_kleene( );

            for( size_t i = 0; i != kl. size( ); ++ i )
               result. insert( kl. sub(i));
         }

         return logic::term( logic::op_kleene_and, 
                             result. begin( ), result. end( ));
      }

   case prf_select:
      {
         auto sel = prf. view_select( );
         auto fm = deduce( sel. parent( ), seq, err );
         if( !fm. has_value( ))
            return fm;

         auto conj = optform( std::move( fm ), "select", seq, err );
         conj. musthave( logic::op_kleene_and );
         if( !conj ) 
            return { };

         auto errsize = err. size( );

         auto kl = conj. value( ). view_kleene( );
         formulaset result; 

         for( size_t i = 0; i != sel. size( ); ++ i )
         {
            if( sel. nr(i) >= kl. size( ))
            {
               auto bld = errorstack::builder( );
               bld << "selected subterm " << sel. nr(i);
               bld << " >= " << kl. size( ); 
               err. push( std::move( bld )); 
            }
            else
               result. insert( kl. sub( sel. nr(i) ));
         } 

         if( err. size( ) > errsize )
         {
            auto bld = printing::makeheader( seq, "select" );
            err. addheader( errsize, std::move( bld ));
         }

         return logic::term( logic::op_kleene_and,
                                result. begin( ), result. end( ));
      }
 
   case prf_conflict:
      {
         auto confl = prf. view_conflict( );

         auto form = deduce( confl. parent( ), seq, err );

         if( !form. has_value( ))
            return form;

         std::vector< logic::term > checked;
         std::vector< logic::term > unchecked;
         unchecked. push_back( form. value( ));
   
         bool c = inconflict( checked, unchecked );

         if( !c )
         {
            auto bld = printing::makeheader( seq, "conflict" );
            bld << "formula does not contain a conflict:\n";
            bld << "  "; printing::pretty( bld, seq, form. value( ));
            bld << "\n";
            err. push( std::move( bld ));
         }

         return logic::term( logic::op_kleene_and, {
            logic::term( logic::op_kleene_or, { } ) } );
      }

   case prf_fake:
      {
         auto res = optform( prf. view_fake( ). goal( ), "fake", seq, err );
         res. make_anf2( );
         res. fake( ); 
         return res. value( ); 
      }

   case prf_show:
      {
         auto show = prf. view_show( ); 
         auto res = deduce( show. prf( ), seq, err );
         for( short unsigned int i = 0; i < 70; ++ i )
            std::cout << '-';
         std::cout << "\n"; 
         std::cout << "this is " << show. comment( ) << ":\n";
         std::cout << seq << "\n";
         if( res. has_value( ))
         {
            std::cout << "Deduced subformula:\n";
            std::cout << "   ";
            printing::pretty( std::cout, seq, res. value( ));
         }
         else
            std::cout << "(proof failed)\n";
         std::cout << "\n\n";
         return res;
      } 
   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check proof term" );
}


