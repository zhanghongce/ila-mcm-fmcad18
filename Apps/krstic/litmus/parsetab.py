
# parsetab.py
# This file is automatically generated. Do not edit.
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = 'ALTERNATIVE W R F FLAG ID RELATION RL FORBIDDEN PERMITTED REQ LC RC VA PA DATA TO EQlitmus : altBlks outcomealtBlks : altblk \n        | altblk altBlksaltblk : ALTERNATIVE instructions relations condsinstructions : instructions instruction \n        | instruction relations : relations relation \n        | relation instruction : ID ID ID ID opcodeopcode : LC inst optionalFlags vablock pablock datablock RC\n            | LC F FLAG RCinst : R \n        | W \n        | optionalFlags : empty\n        | FLAGvablock : LC VA ID ID RCpablock : LC PA ID ID RCdatablock : LC DATA ID RCoutcome : FORBIDDEN \n        | PERMITTED\n        | REQrelation : RELATION RL ID ID TO ID IDconds : conds cond \n        | empty cond : LC PA ID ID RC EQ IDempty :'
    
_lr_action_items = {'TO':([30,],[36,]),'LC':([15,16,19,20,21,23,25,27,32,33,34,38,39,40,45,47,50,56,61,64,],[-27,-8,24,-7,-25,27,-24,-14,-12,-27,-13,44,-16,-15,49,-23,54,-26,-17,-18,]),'F':([27,],[31,]),'DATA':([54,],[59,]),'FORBIDDEN':([1,4,5,15,16,19,20,21,25,47,56,],[-2,10,-3,-27,-8,-4,-7,-25,-24,-23,-26,]),'REQ':([1,4,5,15,16,19,20,21,25,47,56,],[-2,9,-3,-27,-8,-4,-7,-25,-24,-23,-26,]),'VA':([44,],[48,]),'PERMITTED':([1,4,5,15,16,19,20,21,25,47,56,],[-2,12,-3,-27,-8,-4,-7,-25,-24,-23,-26,]),'R':([27,],[32,]),'FLAG':([27,31,32,33,34,],[-14,37,-12,39,-13,]),'PA':([24,49,],[29,53,]),'RELATION':([6,8,14,15,16,20,28,43,47,60,],[-6,17,-5,17,-8,-7,-9,-11,-23,-10,]),'W':([27,],[34,]),'RC':([37,41,55,57,62,63,65,],[43,46,60,61,64,65,-19,]),'RL':([17,],[22,]),'ALTERNATIVE':([0,1,15,16,19,20,21,25,47,56,],[3,3,-27,-8,-4,-7,-25,-24,-23,-26,]),'EQ':([46,],[51,]),'ID':([3,6,7,8,13,14,18,22,26,28,29,35,36,42,43,48,51,52,53,58,59,60,],[7,-6,13,7,18,-5,23,26,30,-9,35,41,42,47,-11,52,56,57,58,62,63,-10,]),'$end':([2,9,10,11,12,],[0,-22,-20,-1,-21,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'pablock':([45,],[50,]),'opcode':([23,],[28,]),'conds':([15,],[19,]),'altblk':([0,1,],[1,1,]),'instruction':([3,8,],[6,14,]),'inst':([27,],[33,]),'litmus':([0,],[2,]),'optionalFlags':([33,],[38,]),'empty':([15,33,],[21,40,]),'relation':([8,15,],[16,20,]),'relations':([8,],[15,]),'cond':([19,],[25,]),'datablock':([50,],[55,]),'outcome':([4,],[11,]),'vablock':([38,],[45,]),'altBlks':([0,1,],[4,5,]),'instructions':([3,],[8,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> litmus","S'",1,None,None,None),
  ('litmus -> altBlks outcome','litmus',2,'p_litmus','litmusParse.py',212),
  ('altBlks -> altblk','altBlks',1,'p_altBlks','litmusParse.py',241),
  ('altBlks -> altblk altBlks','altBlks',2,'p_altBlks','litmusParse.py',242),
  ('altblk -> ALTERNATIVE instructions relations conds','altblk',4,'p_altblk','litmusParse.py',249),
  ('instructions -> instructions instruction','instructions',2,'p_instructions','litmusParse.py',253),
  ('instructions -> instruction','instructions',1,'p_instructions','litmusParse.py',254),
  ('relations -> relations relation','relations',2,'p_relations','litmusParse.py',261),
  ('relations -> relation','relations',1,'p_relations','litmusParse.py',262),
  ('instruction -> ID ID ID ID opcode','instruction',5,'p_instruction','litmusParse.py',269),
  ('opcode -> LC inst optionalFlags vablock pablock datablock RC','opcode',7,'p_opcode','litmusParse.py',284),
  ('opcode -> LC F FLAG RC','opcode',4,'p_opcode','litmusParse.py',285),
  ('inst -> R','inst',1,'p_inst','litmusParse.py',297),
  ('inst -> W','inst',1,'p_inst','litmusParse.py',298),
  ('inst -> <empty>','inst',0,'p_inst','litmusParse.py',299),
  ('optionalFlags -> empty','optionalFlags',1,'p_optionalFlags','litmusParse.py',308),
  ('optionalFlags -> FLAG','optionalFlags',1,'p_optionalFlags','litmusParse.py',309),
  ('vablock -> LC VA ID ID RC','vablock',5,'p_vablock','litmusParse.py',317),
  ('pablock -> LC PA ID ID RC','pablock',5,'p_pablock','litmusParse.py',322),
  ('datablock -> LC DATA ID RC','datablock',4,'p_datablock','litmusParse.py',327),
  ('outcome -> FORBIDDEN','outcome',1,'p_outcome','litmusParse.py',331),
  ('outcome -> PERMITTED','outcome',1,'p_outcome','litmusParse.py',332),
  ('outcome -> REQ','outcome',1,'p_outcome','litmusParse.py',333),
  ('relation -> RELATION RL ID ID TO ID ID','relation',7,'p_relation','litmusParse.py',340),
  ('conds -> conds cond','conds',2,'p_conds','litmusParse.py',349),
  ('conds -> empty','conds',1,'p_conds','litmusParse.py',350),
  ('cond -> LC PA ID ID RC EQ ID','cond',7,'p_cond','litmusParse.py',357),
  ('empty -> <empty>','empty',0,'p_empty','litmusParse.py',364),
]
