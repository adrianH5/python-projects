output_model=./output
# 需要修改到自己的输入目录
if [ ! -d ${output_model} ];then  
    mkdir ${output_model}
fi

export NCCL_P2P_DISABLE=1
cp ./test_lora.sh ${output_model}
deepspeed --include localhost:0 test_clm_lora.py \
    --model_name_or_path meta-llama/Meta-Llama-3-8B-Instruct \
    --train_files  ./final_test_t.csv \
    --validation_files  ./final_test.csv \
    --resume_from_checkpoint /home/gy237/project/llama3/fine_tune/output_lr1e-5/checkpoint-2500 \
    --per_device_train_batch_size 1 \
    --per_device_eval_batch_size 12 \
    --do_train true \
    --do_eval true \
    --use_fast_tokenizer false \
    --output_dir ${output_model} \
    --evaluation_strategy  steps \
    --max_eval_samples 800 \
    --learning_rate 1e-6 \
    --gradient_accumulation_steps 8 \
    --num_train_epochs 5 \
    --warmup_steps 2500 \
    --load_in_bits 4 \
    --lora_r 8 \
    --lora_alpha 32 \
    --target_modules q_proj,k_proj,v_proj,o_proj,down_proj,gate_proj,up_proj \
    --logging_dir ${output_model}/logs \
    --logging_strategy steps \
    --logging_steps 50 \
    --save_strategy steps \
    --preprocessing_num_workers 10 \
    --save_steps 2500 \
    --eval_steps 1 \
    --save_total_limit 2000 \
    --seed 42 \
    --disable_tqdm false \
    --ddp_find_unused_parameters false \
    --block_size 2048 \
    --report_to tensorboard \
    --overwrite_output_dir \
    --deepspeed ds_config_zero2.json \
    --ignore_data_skip true \
    --bf16 \
    --gradient_checkpointing \
    --bf16_full_eval \
    --ddp_timeout 18000000 \
    | tee -a ${output_model}/train.log
    


    
