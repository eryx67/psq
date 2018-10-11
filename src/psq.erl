%%% @author Vladimir G. Sekissov <eryx67@gmail.com>
%%% @copyright (C) 2018, Vladimir G. Sekissov
%%% @doc Priority search queue
%%%
%%% @end
%%% Created : 10 Oct 2018 by Vladimir G. Sekissov <eryx67@gmail.com>

-module(psq).

-export([new/0, singleton/3,
         insert/4, lookup/2, member/2, delete/2, alter/3,
         delete_min/1, find_min/1, alter_min/2,
         psq_size/1, null/1,
         to_list/1, from_list/1,
         fold/3, map/2, keys/1,
         insert_view/4, delete_view/2, min_view/1, at_most_view/2
        ]).

-export_type([maybe/1, psq/0, priority/0]).

-type maybe(V) :: nothing | {just, V}.

-type nat() :: non_neg_integer().

-type key() :: non_neg_integer().

-type priority() :: non_neg_integer().

-type value() :: any().

-type mask() :: non_neg_integer().
%% We store masks as the index of the bit that determines the branching.

-record(bin, { key :: key()
             , prio :: priority()
             , val :: value()
             , mask :: mask()
             , left :: psq()
             , right :: psq()
             }).

-record(tip, { key :: key()
             , prio :: priority()
             , val :: value()
             }).
-type psq() :: nil
             | #tip{}
             | #bin{}.
%% A priority search queue with `integer' keys and priorities.

-spec zero(key(), mask()) -> boolean().
zero(Key, Mask) ->
    Key band Mask == 0.

-spec nomatch(key(), key(), mask()) -> boolean().
nomatch(Key1, Key2, Mask) ->
    MW = mask_w(Mask),
    Key1 band  MW /=  Key2 band MW.

-spec mask_w(nat()) -> nat().
mask_w(V) ->
    bnot (V - 1) bxor V.

-spec branch_mask(key(), key()) -> mask().
branch_mask(Key1, Key2) ->
    highest_bit_mask(Key1 bxor Key2).

highest_bit_mask(0) ->
    0;
highest_bit_mask(I) ->
    highest_bit_mask(I, 1).

highest_bit_mask(I, HBM) when I == 1 ->
    HBM;
highest_bit_mask(I, HBM) ->
    highest_bit_mask(I bsr 1, HBM bsl 1).

%% ------------------------------------------------------------------------------
%%  Query
%% ------------------------------------------------------------------------------

-spec null(psq()) -> boolean().
null(nil) -> true;
null(_)   -> false.

-spec psq_size(psq())-> non_neg_integer().
psq_size(nil) -> 0;
psq_size(#tip{}) -> 1;
psq_size (#bin{left=L, right=R}) ->
    1 + psq_size(L) + psq_size(R).

-spec member(key(), psq()) -> boolean().
member(Key, PSQ) ->
    is_just(lookup(Key, PSQ)).

-spec lookup(key(), psq()) -> maybe({priority(), value()}).
lookup(Key, PSQ) ->
    case PSQ of
        nil ->
            nothing;
        #tip{key=Key, prio=P, val=V} ->
            {just, {P, V}};
        #tip{} ->
            nothing;
        #bin{key=Key, prio=P, val=V} ->
            {just, {P, V}};
        #bin{key=K, mask=M, left=L, right=R} ->
            IsNomatch = nomatch(Key, K, M),
            IsZero = zero(Key, M),
            case {IsNomatch, IsZero} of
                {true, _} ->
                    nothing;
                {_, true} ->
                    lookup(Key, L);
                {_, _} ->
                    lookup(Key, R)
            end
    end.

-spec find_min(psq()) -> maybe({key(), priority(), value()}).
find_min(nil) -> nothing;
find_min(#tip{key=K, prio=P, val=V})       -> {just, {K, P, V}};
find_min(#bin{key=K, prio=P, val=V})       -> {just, {K, P, V}}.

%%------------------------------------------------------------------------------
%%--- Construction
%%------------------------------------------------------------------------------
-spec new() -> psq().
new() ->
    nil.

-spec singleton(key(), priority(), value()) -> psq().
singleton(K, P, V) ->
    #tip{key=K, prio=P, val = V}.


%%------------------------------------------------------------------------------
%% Insertion
%%------------------------------------------------------------------------------
-spec insert(key(), priority(), value(), psq()) -> psq().
insert(K, P, V, PSQ) ->
    unsafe_insert_new(K, P, V, delete(K, PSQ)).

%% Internal function to insert a key that is not present in the priority queue.
-spec unsafe_insert_new(key(), priority(), value(), psq()) -> psq().
unsafe_insert_new(K, P, V, PSQ) ->
    case PSQ of
        nil -> #tip{key=K, prio=P, val=V};
        #tip{key=K1, prio=P1, val=V1} ->
            if {P, K} < {P1, K1} ->
                    link(K, P, V, K1, PSQ, nil);
               true ->
                    link(K1, P1, V1, K, #tip{key=K, prio=P, val=V}, nil)
            end;
        #bin{key=K1, prio=P1, val=V1, mask=M, left=L, right=R} ->
            IsNomatch = nomatch(K, K1, M),
            if IsNomatch ->
                    if {P, K} < {P1, K1} ->
                            link(K, P, V, K1, PSQ, nil);
                       true ->
                            link(K1, P1, V1, K, #tip{key=K, prio=P, val=V}, merge(M, L, R))
                    end;
               true ->
                    if {P, K} < {P1, K1} ->
                            IsZero = zero(K1, M),
                            if IsZero ->
                                    #bin{key=K, prio=P, val=V, mask=M,
                                         left=unsafe_insert_new(K1, P1, V1, L), right=R
                                        };
                               true ->
                                    #bin{key=K, prio=P, val=V, mask=M,
                                         left=L, right=unsafe_insert_new(K1, P1, V1, R)
                                        }
                            end;
                       true ->
                            IsZero = zero(K, M),
                            if IsZero ->
                                    #bin{key=K1, prio=P1, val=V1, mask=M,
                                         left=unsafe_insert_new(K, P, V, L), right=R
                                        };
                               true ->
                                    #bin{key=K1, prio=P1, val=V1, mask=M,
                                         left=L, right=unsafe_insert_new(K, P, V, R)
                                        }
                            end
                    end
            end
    end.

-spec link(key(), priority(), value(), key(), psq(), psq()) -> psq().
link(K, P, V, K1, Q1, Q2) ->
    BM = branch_mask(K, K1),
    IsZero = zero(BM, K1),
    if IsZero ->
            #bin{key=K, prio=P, val=V, mask=BM, left=Q1, right=Q2};
       true ->
            #bin{key=K, prio=P, val=V, mask=BM, left=Q2, right=Q1}
    end.

%%------------------------------------------------------------------------------
%% Delete/Alter
%%------------------------------------------------------------------------------

%% @doc Delete a key and its priority and value from the queue. When
%% the key is not a member of the queue, the original queue is returned.
%% @end
-spec delete(key(), psq()) -> psq().
delete(K, PSQ) ->
    case PSQ of
        nil ->
            nil;
        #tip{key=K} ->
            nil;
        #tip{} ->
            PSQ;
        #bin{key=K, mask=M, left=L, right=R} ->
            merge(M, L, R);
        #bin{key=K1, prio=P1, val=V1, mask=M, left=L, right=R} ->
            IsNoMatch = nomatch(K, K1, M),
            IsZero = zero(K, M),
            case {IsNoMatch,IsZero} of
                {true, _} ->
                    PSQ;
                {_, true} ->
                    bin_shrink_l(K1, P1, V1, M, delete(K, L), R);
                {false, false} ->
                    bin_shrink_r(K1, P1, V1, M, L, delete(K, R))
            end
    end.

%% @doc Delete the binding with the least priority, and return the
%% rest of the queue stripped of that binding. In case the queue is empty, the
%% empty queue is returned again.
%% @end
-spec delete_min(psq()) -> psq().
delete_min(PSQ) ->
    case min_view(PSQ) of
        nothing -> PSQ;
        {just, {_, _, _, PSQ1}} -> PSQ1
    end.

%% @doc Alters the value `Value' at `Key',
%% or absence thereof. Can be used to insert, delete, or update a value
%% in a queue. It also allows you to calculate an additional value `B'.
-spec alter(fun ((maybe({Prio, Value})) -> {B, maybe({Prio, Value})}), Key, PSQ) ->
                   {B, PSQ} when
      Key :: key()
      , Value :: value()
      , Prio :: priority()
      , PSQ :: psq()
      , B :: any().
alter(F, K, PSQ) ->
    {PSQ1, MV} = case delete_view(K, PSQ) of
                     nothing ->
                         {PSQ, nothing};
                     {just, {P, V, PSQ11}} ->
                         {PSQ11, {just, {P, V}}}
                 end,
    {B, MV1} = F(MV),
    PSQ2 = case MV1 of
               nothing -> PSQ1;
               {just, {P1, V1}} ->
                   unsafe_insert_new(K, P1, V1, PSQ1)
           end,
    {B, PSQ2}.

%% A variant of `alter' which works on the element with the
%% minimum priority. Unlike `alter', this variant also allows you to change the
%% key of the element.
-spec alter_min(fun ((maybe({key(), priority(), value()})) -> {B, maybe({key(), priority(), value()})}), psq())
               -> {B, psq()}.
alter_min(F, PSQ) ->
    case PSQ of
        nil ->
            case F(nothing) of
                {B, nothing}           -> {B, nil};
                {B, {just, {K1, P1, V1}}} -> {B, #tip{key=K1, prio=P1, val=V1}}
            end;
        #tip{key=K, prio=P, val=V} ->
            case F({just, {K, P, V}}) of
                {B, nothing}           -> {B, nil};
                {B, {just, {K1, P1, V1}}} -> {B, #tip{key=K1, prio=P1, val=V1}}
            end;
        #bin{key=K, prio=P, val=V, mask=M, left=L, right=R} ->
            case F({just, {K, P, V}}) of
                {B, nothing} ->
                    {B, merge(M, L, R)};
                {B, {just, {K1, P1, V1}}} when K /= K1 ->
                    {B, insert(K1, P1, V1, merge(M, L, R))};
                {B, {just, {K, P1, V1}}} when P1 =< P ->
                    {B, #bin{key=K, prio=P1, val=V1, mask=M, left=L, right=R}};
                {B, {just, {K, P1, V1}}} ->
                    {B, unsafe_insert_new(K, P1, V1, merge(M, L, R))}
            end
    end.

-spec bin_shrink_l(key(), priority(), value(), mask(), psq(), psq()) -> psq().
bin_shrink_l(K, P, V, M, nil, R) ->
    case R of
        nil -> #tip{key=K, prio=P, val=V};
        _ -> #bin{key=K, prio=P, val=V, mask=M, left=nil, right=R}
    end;
bin_shrink_l(K, P, V, M, L, R) ->
    #bin{key=K, prio=P, val=V, mask=M, left=L, right=R}.

-spec bin_shrink_r(key(), priority(), value(), mask(), psq(), psq()) -> psq().
bin_shrink_r(K, P, V, M, L, nil) ->
    case L of
        nil -> #tip{key=K, prio=P, val=V};
        _ -> #bin{key=K, prio=P, val=V, mask=M, left=L, right=nil}
    end;
bin_shrink_r(K, P, V, M, L, R) ->
    #bin{key=K, prio=P, val=V, mask=M, left=L, right=R}.

%%------------------------------------------------------------------------------
%%-- Lists
%%------------------------------------------------------------------------------

%% Build a queue from a list of (key, priority, value) tuples.
%% If the list contains more than one priority and value for the same key, the
%% last priority and value for the key is retained.
-spec from_list([{key(), priority(), value()}]) -> psq().
from_list(KPVs) ->
    lists:foldl(fun ({K, P, V}, Acc) ->
                        insert(K, P, V, Acc)
                end, new(), KPVs).

%% Convert a queue to a list of (key, priority, value) tuples. The
%% order of the list is not specified.
-spec to_list (psq()) -> [{key(), priority(), value()}].
to_list(PSQ) ->
    to_list(PSQ, []).

to_list(nil, Acc) ->
    Acc;
to_list(#tip{key=K1, prio=P1, val=V1}, Acc) ->
    [{K1, P1, V1}| Acc];
to_list(#bin{key=K1, prio=P1, val=V1, left=L, right=R}, Acc) ->
    [{K1, P1, V1}| to_list(L, to_list(R, Acc))].

%% Obtain the list of present keys in the queue.
-spec keys(psq()) -> [key()].
keys(PSQ) ->
    [K || {K, _, _} <- to_list(PSQ)].

%%------------------------------------------------------------------------------
%% Views
%%------------------------------------------------------------------------------

%% @doc Insert a new key, priority and value into the queue. If the key
%% is already present in the queue, then the evicted priority and value can be
%% found the first element of the returned tuple.
%% @end
-spec insert_view(key(), priority(), value(), psq()) -> {maybe({priority(), value()}), psq()}.
insert_view(K, P, V, PSQ) ->
    case delete_view(K, PSQ) of
        nothing ->
            {nothing, unsafe_insert_new(K, P, V, PSQ)};
        {just, {P1, V1, PSQ1}} ->
            {{just, {P1, V1}}, unsafe_insert_new(K, P, V, PSQ1)}
    end.

%% @doc Delete a key and its priority and value from the queue. If
%% the key was present, the associated priority and value are returned in
%% addition to the updated queue.
%% @end
-spec delete_view(key(), psq()) -> maybe({priority(), value(), psq()}).
delete_view(K, PSQ) ->
    case delete_view_1(K, PSQ) of
      {nothing, _} -> nothing;
      {Q, {just, {P, V}}} -> {just, {P, V, Q}}
    end.

delete_view_1(K, PSQ) ->
    case PSQ of
        nil -> { nil, nothing };
        #tip{key=K, prio=P1, val=V1} ->
            { nil, {just, {P1, V1}} };
        #tip{} ->
            { PSQ, nothing };
        #bin{key=K, prio=P1, val=V1, mask=M, left=L, right=R} ->
            {merge(M, L, R), {just, {P1, V1}}};
        #bin{key=K1, prio=P1, val=V1, mask=M, left=L, right=R} ->
            IsNomatch = nomatch(K, K1, M),
            IsZero = zero(K, M),
            case {IsNomatch, IsZero} of
                {true, _} ->
                    { PSQ, nothing };
                {_, true} ->
                    {L1, MPV} = delete_view_1(K, L),
                    {bin_shrink_l(K1, P1, V1, M, L1, R), MPV};
                {false, false} ->
                    {R1, MPV } = delete_view_1(K, R),
                    {bin_shrink_r(K1, P1, V1, M, L, R1), MPV}
            end
    end.

%% Retrieve the binding with the least priority, and the
%% rest of the queue stripped of that binding.
-spec min_view(psq()) -> maybe({key(), priority(), value(), psq()}).
min_view(PSQ) ->
    case PSQ of
        nil -> nothing;
        #tip{key=K, prio=P, val=V} ->
            {just, {K, P, V, nil}};
        #bin{key=K, prio=P, val=V, mask=M, left=L, right=R} ->
            {just, {K, P, V, merge(M, L, R)}}
    end.

%% @doc Return a list of elements ordered by key whose priorities are at most @pt@,
%% and the rest of the queue stripped of these elements.  The returned list of
%% elements can be in any order: no guarantees there.
%% @end
-spec at_most_view (priority(), psq()) -> {[{key(), priority(), value()}], psq()}.
at_most_view(PQ, PSQ) ->
    at_most_view(PQ, PSQ, []).

at_most_view(_PQ, nil, Acc) ->
    {Acc, nil};
at_most_view(PQ, Q=#tip{prio=P}, Acc) when P > PQ ->
    {Acc, Q};
at_most_view(_PQ, #tip{key=K, prio=P, val=V}, Acc) ->
    {[{K, P, V}|Acc], nil};
at_most_view(PQ, Q=#bin{prio=P}, Acc) when P > PQ ->
    {Acc, Q};
at_most_view(PQ, #bin{key=K, prio=P, val=V, mask=M, left=L, right=R}, Acc) ->
    {Acc1,  L1} = at_most_view(PQ, L, Acc),
    {Acc2,  R1} = at_most_view(PQ, R, Acc1),
    {[{K, P, V}|Acc2], merge(M, L1, R1)}.


%%------------------------------------------------------------------------------
%% Traversal
%%------------------------------------------------------------------------------

%% @doc Modify every value in the queue.
%% @end
-spec map(fun ((key(), priority(), value()) -> value()), psq()) -> psq().
map(_F, nil) ->
    nil;
map(F, #tip{key=K, prio=P, val=V}) ->
    #tip{key=K, prio=P, val=F(K, P, V)};
map(F, #bin{key=K, prio=P, val=V, mask=M, left=L, right=R}) ->
    #bin{key=K, prio=P, val=F(K, P, V), mask=M, left=map(F, L), right=map(F, R)}.

%% @doc Fold over every key, priority and value in the queue. The order
%% in which the fold is performed is not specified.
%% @end
-spec fold(fun ((key(), priority(), value(), any()) -> any()), any(), psq()) -> any().
fold(_F, Acc, nil) ->
    Acc;
fold(F, Acc, #tip{key=K1, prio=P1, val=V1}) ->
    F(K1, P1, V1, Acc);
fold(F, Acc, #bin{key=K1, prio=P1, val=V1, left=L, right=R}) ->
    Acc1 = F(K1, P1, V1, Acc),
    Acc2 = fold(F, Acc1, L),
    Acc3 = fold(F, Acc2, R),
    Acc3.

%% Internal function that merges two disjoint PSQs that share the
%% same prefix mask.
-spec merge(mask(), psq(), psq()) -> psq().
merge(_M, nil, R) ->
    R;
merge(_M, L=#tip{}, nil) ->
    L;
merge(M, _L=#tip{key=LK, prio=LP, val=LV}, R=#tip{key=RK, prio=RP}) when {LP, LK} < {RP, RK} ->
    #bin{key=LK, prio=LP, val=LV, mask=M, left=nil, right=R};
merge(M, L=#tip{}, #tip{key=RK, prio=RP, val=RV}) ->
    #bin{key=RK, prio=RP, val=RV, mask=M, left=L, right=nil};
merge(M, _L=#tip{key=LK, prio=LP, val=LV}, R=#bin{key=RK, prio=RP})
  when {LP, LK} < {RP, RK} ->
    #bin{key=LK, prio=LP, val=LV, mask=M, left=nil, right=R};
merge(M, L=#tip{}, #bin{key=RK, prio=RP, val=RV, mask=RM, left=RL, right=RR}) ->
    #bin{key=RK, prio=RP, val=RV, mask=M, left=L, right=merge(RM, RL, RR)};
merge(M, L=#bin{key=LK, prio=LP, val=LV, mask=LM, left=LL, right=LR}, R) ->
      case R of
          nil ->
              L;
          #tip{key=RK, prio=RP} when {LP, LK} < {RP, RK} ->
              #bin{key=LK, prio=LP, val=LV, mask=M, left=merge(LM, LL, LR), right=R};
          #tip{key=RK, prio=RP, val=RV} ->
              #bin{key=RK, prio=RP, val=RV, mask=M, left=L, right=nil};
          #bin{key=RK, prio=RP} when {LP, LK} < {RP, RK} ->
              #bin{key=LK, prio=LP, val=LV, mask=M, left=merge(LM, LL, LR), right=R};
          #bin{key=RK, prio=RP, val=RV, mask=RM, left=RL, right=RR} ->
              #bin{key=RK, prio=RP, val=RV, mask=M, left=L, right=merge(RM, RL, RR)}
      end.

is_just(nothing) -> false;
is_just({just, _}) -> true.

%%--------------------------
%% Tests
%%--------------------------
-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

-define(MAX_WORD64, 16#ffffffffffffffff).

new_test() ->
    ?assertEqual(nil, psq:new()).

singleton_test() ->
    ?assertEqual(#tip{key=1, prio=2, val=3}, psq:singleton(1, 2, 3)).

psq_test_() ->
    TestF =
        fun (_, KPVs) ->
                [
                 {"Insert",
                  ?_test(begin
                             PSQ1 = psq_insert(KPVs),
                             ?assertEqual(KPVs, lists:keysort(1, psq:to_list(PSQ1))),
                             PSQ2 = psq_insert(KPVs, PSQ1),
                             ?assertEqual(KPVs, lists:keysort(1, psq:to_list(PSQ2)))
                         end)
                 },
                 {"Lookup",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (PSQ) ->
                           [?_test([?assertEqual({just, {P, V}}, psq:lookup(K, PSQ)) || {K, P, V} <- KPVs])]
                   end
                  }
                 },
                 {"Member",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (PSQ) ->
                           [?_test([?assertEqual(true, psq:member(K, PSQ)) || {K, _P, _V} <- KPVs]),
                            ?_test([?assertEqual(false, psq:member(K, PSQ)) ||
                                       K <- integer_list(100),
                                       lists:keymember(K, 1, KPVs) == false])
                           ]
                   end
                  }
                 },
                 {"Delete",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (InPSQ) ->
                           [?_test(begin
                                       PSQ = lists:foldl(fun ({K, _P, _V}, PSQ1) ->
                                                                 ?assertEqual(true, psq:member(K, PSQ1)),
                                                                 PSQ2 = psq:delete(K, PSQ1),
                                                                 ?assertEqual(false, psq:member(K, PSQ2)),
                                                                 PSQ2
                                                         end, InPSQ, KPVs),
                                       ?assertEqual(true, psq:null(PSQ))
                                   end)
                           ]
                   end
                  }
                 },
                 {"Size",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (PSQ) ->
                           [?_assertEqual(length(KPVs), psq:psq_size(PSQ))]
                   end
                  }
                 },
                 {"Keys",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (PSQ) ->
                           [?_assertEqual(lists:sort([K || {K, _, _} <- KPVs]), lists:sort(psq:keys(PSQ)))]
                   end
                  }
                 },
                 {"Map",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (PSQ) ->
                           [?_assertEqual(lists:sort(KPVs),
                                         lists:sort([V ||
                                                        {_, _, V} <- psq:to_list(psq:map(fun (K, P, V) ->
                                                                                                 {K, P, V}
                                                                                         end, PSQ))]))
                           ]
                   end
                  }
                 },
                 {"Fold",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (PSQ) ->
                           [?_assertEqual(lists:sum([V || {_, _, V} <- KPVs]),
                                          psq:fold(fun (_K, _P, V, Acc) -> V + Acc end,
                                                   0, PSQ))
                           ]
                   end
                  }
                 },
                 {"Alter modify",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (PSQ) ->
                           [?_test(case KPVs of
                                       [] ->
                                           ?assertEqual(nothing, psq:find_min(PSQ));
                                       [{EK, EP, EV}|_] ->
                                           Res1 = psq:alter(fun ({just, {P, V}}) ->
                                                                    {V, {just, {P+1, V+2}}}
                                                            end, EK, PSQ),
                                           ?assertMatch({EV, _}, Res1),
                                           {EV, PSQ1} = Res1,
                                           ?assertEqual({just, {EP+1, EV+2}}, psq:lookup(EK, PSQ1))
                                   end)
                           ]
                   end
                  }
                 },
                 {"Alter delete",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (PSQ) ->
                           [?_test(case KPVs of
                                       [] ->
                                           ?assertEqual(nothing, psq:find_min(PSQ));
                                       [{EK, _EP, EV}|_] ->
                                           Res2 = psq:alter(fun ({just, {_P, V}}) ->
                                                                    {V, nothing}
                                                            end, EK, PSQ),
                                           {EV, PSQ2} = Res2,
                                           ?assertEqual(nothing, psq:lookup(EK, PSQ2))
                                   end)
                           ]
                   end
                  }
                 },
                 %% find_min/1, delete_min/1, alter_min/2,
                 {"Minimal priority element",
                  {setup,
                   fun () -> psq:from_list(KPVs) end,
                   fun (PSQ) ->
                           SortedKPVs = lists:sort(fun ({K1, P1, _V1}, {K2, P2, _V2}) ->
                                                           {P1, K1} =< {P2, K2}
                                                   end, KPVs),
                           [?_test(case SortedKPVs of
                                       [] ->
                                           ?assertEqual(nothing, psq:find_min(PSQ));
                                       [MinE={MK, MP, MV}|_] ->
                                           ?assertEqual({just, MinE}, psq:find_min(PSQ)),
                                           ?assertEqual(lists:sort(lists:delete(MinE, KPVs)),
                                                        lists:sort(psq:to_list(psq:delete_min(PSQ)))),
                                           Res1 = psq:alter_min(fun ({just, {K, P, V}}) ->
                                                                        {V, {just, {K, P+1, V+2}}}
                                                               end, PSQ),
                                           ?assertMatch({MV, _}, Res1),
                                           {MV, PSQ1} = Res1,
                                           ?assertEqual({just, {MP+1, MV+2}}, psq:lookup(MK, PSQ1)),

                                           Res2 = psq:alter_min(fun ({just, {_K, _P, V}}) ->
                                                                        {V, nothing}
                                                               end, PSQ),
                                           {MV, PSQ2} = Res2,
                                           ?assertEqual(nothing, psq:lookup(MK, PSQ2))
                                   end)
                           ]
                   end
                  }
                 }
                ]
        end,
    {foreachx,
     fun ({N, NP}) ->
             _ = crypto:rand_seed(),
             mk_kpvs(N, NP)
     end,
     [{{N, NP}, TestF} || N <- lists:seq(1, 100), NP <- lists:seq(1, 10)]
    }.

bench_test_() ->
    {setup,
    fun () ->
            mk_kpvs(10000, 10)
    end,
    fun (KPVs) ->
            [?_test(
               begin
                   PSQ = psq:from_list(KPVs),
                   ?debugTime(io_lib:fwrite("PSQ: inserting ~p elements", [length(KPVs)]),
                              psq_insert(KPVs, PSQ)),
                   ?debugTime("PSQ: get element with minimal priority 1000 times",
                              lists:foreach(fun (_) -> psq:min_view(PSQ) end, lists:seq(1, 1000))),
                   ?debugTime("PSQ: change priority of element with minimal priority 1000 times",
                              lists:foldl(fun (_, PSQ0) ->
                                                  {_, PSQ1} =
                                                      psq:alter_min(fun ({just, {K, P, V}}) ->
                                                                            {{K, P, V}, {just, {K, P+10, V}}}
                                                                    end, PSQ0),
                                                  PSQ1
                                          end, PSQ, lists:seq(1, 1000))),
                   ?debugTime(io_lib:fwrite("PSQ: update priority for ~p elements", [length(KPVs)]),
                              lists:foldl(fun ({K, _, _}, PSQ0) ->
                                                  {_, PSQ1} = psq:alter(fun ({just, {P, V}}) ->
                                                                                {V, {just, {P+1, V}}}
                                                                        end, K, PSQ0),
                                                 PSQ1
                                          end, PSQ, KPVs)),

                   ?assertEqual(ok, ok)
               end)
            ]
    end
    }.

psq_insert(KPVs) ->
    psq_insert(KPVs, psq:new()).

psq_insert(KPVs, InPSQ) ->
    PSQ = lists:foldl(fun({K, P, V}, Q) ->
                              psq:insert(K, P, V, Q)
                      end, InPSQ, shuffle(KPVs)),
    PSQ.

mk_kpvs(N) ->
    mk_kpvs(N, N).

mk_kpvs(N, PN) ->
    Ks = lists:usort(integer_list(N)),
    Ps = integer_list(length(Ks), PN),
    Vs = integer_list(length(Ks)),
    KPVs = lists:zip3(Ks, Ps, Vs),
    KPVs.

integer_list(N) ->
    integer_list(N, ?MAX_WORD64).

integer_list(N, Max) ->
    [rand:uniform(Max) || _ <- lists:seq(1, N)].

shuffle(List) ->
    [X||{_,X} <- lists:keysort(1, [{rand:uniform(), N} || N <- List])].

-endif.
