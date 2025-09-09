import Std.Data.List.Basic
import Std.Data.RBMap
import Std.Data.HashMap
-- 假设我们有一个简单的 StateM 实现
abbrev StateM (σ : Type) (α : Type) := σ → (α × σ)

instance : Monad (StateM σ) where
  pure x := λ s => (x, s)
  bind x f := λ s =>
    let (a, s') := x s
    f a s'

def get : StateM σ σ := λ s => (s, s)
def set (s' : σ) : StateM σ Unit := λ _ => ((), s')
def modify (f : σ → σ) : StateM σ Unit := λ s => ((), f s)

-- ... (之前的 Parameter, ParamGroup 等定义保持不变) ...

structure ZeroOptimizer where
  dp_process_group : dist
  offload_param : Bool
  params_in_nvme_and_cpu : Bool
  fp16_groups : List (List Parameter)
  fp16_partitioned_groups : List (List Nat)
  sub_group_to_group_id : Std.HashMap Nat Nat -- 改用 HashMap 为例
  fp16_partitioned_groups_flat_numel : List Nat
  fp16_partitioned_groups_flat_id : List (List Nat)
  groups_padding : List (List Nat)
  lp_param_buffer : Option Nat
  param_groups_fp16_flat_cpu_memory : List Nat
  fp16_partitioned_groups_flat : List (Option Nat)

-- 定义一个辅助函数，用于在 StateM 中更新多个字段
def _process_sub_group (param_group_idx : Nat) (sub_group : List Parameter) : StateM ZeroOptimizer Unit := do
  let s ← get
  let sub_group_idx := s.fp16_groups.length

  -- 使用 modify 来更新复杂的记录结构
  modify (λ s => {
    s with
    fp16_groups := s.fp16_groups ++ [sub_group],
    fp16_partitioned_groups := s.fp16_partitioned_groups ++ [sub_group.map (λ p => p.ds_tensor)],
    sub_group_to_group_id := s.sub_group_to_group_id.insert sub_group_idx param_group_idx, -- 假设 HashMap 有 insert
    fp16_partitioned_groups_flat_numel := s.fp16_partitioned_groups_flat_numel ++ [sub_group.foldl (λ sum p => sum + p.partition_numel ()) 0],
    fp16_partitioned_groups_flat_id := s.fp16_partitioned_groups_flat_id ++ [sub_group.map (λ p => p.ds_id)],
    groups_padding := s.groups_padding ++ [
        if dist.get_rank s.dp_process_group == dist.get_world_size s.dp_process_group - 1 then
          sub_group.map (λ p => p.padding_size ())
        else
          sub_group.map (λ _ => 0)
      ]
  })

def _create_fp16_partitions_with_defragmentation (self : ZeroOptimizer) (fp16_param_groups : List FP16ParamGroup) : ZeroOptimizer :=
  let _ := dist.barrier self.dp_process_group

  let param_groups : List (List (List Parameter)) :=
    fp16_param_groups.map (λ param_group => self._create_fp16_sub_groups param_group.params)

  -- 1. 初始化一个“初始状态”，其字段为空列表或初始值，但保留原状态的一些配置（如 dp_process_group）
  let init_state : ZeroOptimizer := {
    dp_process_group := self.dp_process_group,
    offload_param := self.offload_param,
    params_in_nvme_and_cpu := self.params_in_nvme_and_cpu,
    fp16_groups := [],
    fp16_partitioned_groups := [],
    sub_group_to_group_id := Std.mkHashMap,
    fp16_partitioned_groups_flat_numel := [],
    fp16_partitioned_groups_flat_id := [],
    groups_padding := [],
    lp_param_buffer := none,
    param_groups_fp16_flat_cpu_memory := self.param_groups_fp16_flat_cpu_memory, -- 保留可能已有的配置？
    fp16_partitioned_groups_flat := []
  }

  -- 2. 使用 StateM 来处理所有嵌套循环和状态更新
  let state_after_loops : ZeroOptimizer :=
    (param_groups.foldlM (λ param_group_idx param_group => do
        param_group.foldlM (λ _ sub_group => do
          _process_sub_group param_group_idx sub_group
        ) ()
        pure (param_group_idx + 1)
      ) 0).run init_state |>.snd -- 执行 StateM 计算，并取最终状态

  -- 3. 根据条件进行后续处理
  let final_state :=
    if not state_after_loops.offload_param then
      -- 不卸载参数的分支，同样返回一个新状态
      let parameter_partitions := state_after_loops._get_parameter_partitions
      let lp_param_buffer := defragment parameter_partitions
      { (state_after_loops._set_fp16_partitioned_groups_flat) with lp_param_buffer := some lp_param_buffer }
    else
      -- ... 类似地，使用 StateM 或函数来管理 else 分支中的复杂状态更新 ...
      state_after_loops

  -- 4. 检查是否需要创建重用缓冲区
  let should_create := final_state.fp16_partitioned_groups_flat.any Option.isNone
  if should_create then
    -- ... 计算 max_partition_numel ...
    -- 返回最终状态，可能更新了某个字段
    final_state -- 假设这里只是返回，没有修改
  else
    final_state

-- 假设的 run 函数
abbrev StateM.run (x : StateM σ α) (s : σ) : (α × σ) := x s
