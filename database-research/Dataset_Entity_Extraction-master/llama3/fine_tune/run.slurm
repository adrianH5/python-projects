#!/bin/bash
#SBATCH --partition=gpu
#SBATCH --job-name=fine_tune_llama3_0
#SBATCH --output=/home/gy237/project/llama3/fine_tune/slrum_output/fine_tune_llama3_0.out
#SBATCH --ntasks=1 --nodes=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=512G
#SBATCH --gpus=a100:2
#SBATCH --time=48:00:00
#SBATCH --mail-type=ALL

echo '-------------------------------------------------'
echo "Job Name: ${SLURM_JOB_NAME}"
echo "I have ${SLURM_CPUS_ON_NODE} CPUs on node $(hostname -s) on partition ${SLURM_JOB_PARTITION}"
echo Running on host $(hostname)
echo Time is $(date)
echo SLURM_NODES are $(echo ${SLURM_NODELIST})
echo "WorkDir is ${SLURM_SUBMIT_DIR}"
echo '-------------------------------------------------'
echo -e '\n\n'

source /home/gy237/anaconda3/bin/activate ft_llama3
echo PATH: $PATH
echo LD_LIBRARY_PATH: $LD_LIBRARY_PATH
echo CUDA_HOME: $CUDA_HOME
$CUDA_HOME/bin/nvcc -V
echo '-------------------------------------------------'
echo -e '\n\n'

sh finetune_lora.sh