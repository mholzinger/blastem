#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "32x.h"

/* FIFOSTAT (mholzinger fork, diagnostic): DREQ FIFO event counts, printed by run_dumps */
uint32_t fifostat[8];
uint32_t fbxstat[8]; /* [0] 68K FB word writes [1] dropped (FM=1) [2] FM raised by 68K [3] FM raised by SH-2 [4] FM cleared by SH-2 [5] FM cleared by 68K [6] 68K FB byte writes [7] byte writes dropped */ /* [0] 68K fifo writes [1] writes while FULL (oldest evicted) [2] writes with 68S clear (ignored) [3] SH-2 fifo reads [4] reads while empty/68S clear (returned 0) [5] 68S set [6] 68S clear by 68K [7] 68S auto-clear (LEN=0) */
/* TRACE HOOKS (mholzinger fork, 2026-09-23): --trace-comm / --trace-flip / --trace-dreq FILE,
 * ares-headless's columns so the two emulators diff directly:
 *   comm: frame,source,comm,value,v,h        source m68k/shm/shs
 *   flip: frame,event,source,select,vcounter,deferred   write rows = FS write requests, flip rows = the change
 *   dreq: frame,event,source,value,v,h       start/push/miss/read/end
 * v,h are the MD VDP beam at the event (BlastEm: vcounter, hslot*2). */
#include "vdp.h"
FILE *trace_comm, *trace_flip, *trace_dreq;
uint32_t s32x_trace_frame;
vdp_context *s32x_trace_vdp;
const char *s32x_trace_src = "m68k";
static inline void trace_vh(uint32_t *v, uint32_t *h)
{
	*v = s32x_trace_vdp ? s32x_trace_vdp->vcounter : 0;
	*h = s32x_trace_vdp ? (uint32_t)s32x_trace_vdp->hslot * 2 : 0;
}
static inline void trace_comm_row(const char *src, uint32_t comm, uint16_t value)
{
	uint32_t v, h; trace_vh(&v, &h);
	fprintf(trace_comm, "%u,%s,%u,0x%04x,0x%03x,0x%02x\n", s32x_trace_frame, src, comm, value, v, h);
}
static inline void trace_dreq_row(const char *event, const char *src, uint32_t value)
{
	uint32_t v, h; trace_vh(&v, &h);
	fprintf(trace_dreq, "%u,%s,%s,%u,0x%03x,0x%02x\n", s32x_trace_frame, event, src, value, v, h);
}
void s32x_trace_flip_row(const char *event, const char *src, uint32_t select, uint32_t vcounter, uint32_t deferred)
{
	if (!trace_flip) return;
	fprintf(trace_flip, "%u,%s,%s,%u,%u,%u\n", s32x_trace_frame, event, src, select, vcounter, deferred);
}

#include "sh7095.h"
#include "genesis.h"
#include "sega_mapper.h"
#include "blastem.h"
#include "util.h"
#include "debug.h"

#define MAX_SH2_CYCLES 2000

#ifdef DO_DEBUG_PRINT
#define dprintf printf
#else
#define dprintf
#endif

void pwm_fifo_write(pwm_fifo *fifo, uint16_t *status, uint16_t value)
{
	fifo->fifo[fifo->write++] = value & 0xFFF;
	fifo->write %= 3;
	if (*status & BIT_PWM_FULL) {
		//FIFO was already full, oldest value was overwritten so advance read
		fifo->read++;
		fifo->read %= 3;
	} else  if (fifo->read == fifo->write) {
		*status |= BIT_PWM_FULL;
	}
	*status &= ~BIT_PWM_EMPTY;
}

void pwm_fifo_read(pwm_fifo *fifo, uint16_t *status, uint16_t cycle, int16_t *out)
{
	if (!(*status & BIT_PWM_EMPTY)) {
		uint16_t sample = fifo->fifo[fifo->read++];
		if (sample > cycle) {
			sample = cycle;
		}
		*out =  sample * 0x200 / cycle - 0x100;
		fifo->read %= 3;
		if (fifo->read == fifo->write) {
			*status |= BIT_PWM_EMPTY;
		} else {
			*status &= ~BIT_PWM_FULL;
		}
	}
}

#define PWM_DECIMATE 64

static uint32_t pwm_tick(s32x *mars, uint32_t ticks)
{
	if (ticks >= mars->pwm_decimate) {
		ticks = mars->pwm_decimate;
		mars->pwm_counter -= mars->pwm_decimate;
		mars->pwm_left_accum += mars->pwm_left * mars->pwm_decimate;
		mars->pwm_right_accum += mars->pwm_right * mars->pwm_decimate;
		render_put_stereo_sample(mars->pwm, mars->pwm_left_accum, mars->pwm_right_accum);
		if (mars->scope) {
			scope_add_sample(mars->scope, mars->scope_left, mars->pwm_left_accum, 0);
			scope_add_sample(mars->scope, mars->scope_right, mars->pwm_right_accum, 0);
		}
		mars->pwm_left_accum = mars->pwm_right_accum = 0;
		mars->pwm_decimate = PWM_DECIMATE;
	} else {
		mars->pwm_left_accum += mars->pwm_left * ticks;
		mars->pwm_right_accum += mars->pwm_right * ticks;
		mars->pwm_decimate -= ticks;
		mars->pwm_counter -= ticks;
	}
	return ticks;
}

static void s32x_pwm_run(s32x *mars, uint32_t target)
{
	if (target <= mars->pwm_cycle) {
		return;
	}
	uint32_t ticks = (target - mars->pwm_cycle) / 7;
	mars->pwm_cycle += 7 * ticks;
	if (mars->pwm_cycle < target) {
		ticks++;
		mars->pwm_cycle += 7;
	}
	if (mars->regs[S32X_PWM_CTRL] & S32X_PWM_LRMD) {
		while (ticks)
		{
			if (mars->pwm_counter == 2) {
				uint16_t cycle = mars->pwm_counter = mars->regs[S32X_PWM_CYCLE];
				if (!cycle) {
					cycle = 0x1000;
				}
				switch (mars->regs[S32X_PWM_CTRL] & 3)
				{
				case 1:
					pwm_fifo_read(&mars->fifo_left, mars->regs + S32X_PWM_WIDTH_L, cycle, &mars->pwm_left);
					break;
				case 2:
					pwm_fifo_read(&mars->fifo_right, mars->regs + S32X_PWM_WIDTH_R, cycle, &mars->pwm_left);
					break;
				//TODO: what happens if the illegal 3 value is used
				}
				switch (mars->regs[S32X_PWM_CTRL] >> 2 & 3)
				{
				case 1:
					pwm_fifo_read(&mars->fifo_right, mars->regs + S32X_PWM_WIDTH_R, cycle, &mars->pwm_right);
					break;
				case 2:
					pwm_fifo_read(&mars->fifo_left, mars->regs + S32X_PWM_WIDTH_L, cycle, &mars->pwm_right);
					break;
				}
				mars->pwm_timer--;
				mars->pwm_timer &= 0xF;
				//TODO: test where the PWM int mask is applied
				if (!mars->pwm_timer) {
					mars->pwm_main_int_pending = mars->pwm_sub_int_pending = 1;
					mars->pwm_timer = mars->regs[S32X_PWM_CTRL] >> 8 & 0xF;
				}
				if (mars->regs[S32X_PWM_CTRL] & BIT_PWM_RTP) {
					sh7095_assert_dreq1(mars->main);
					sh7095_assert_dreq1(mars->sub);
				}
				ticks -= pwm_tick(mars, 1);
			} else if (mars->pwm_counter != 1) {
				if (mars->pwm_counter > 2 + mars->pwm_decimate || !mars->pwm_counter) {
					ticks -= pwm_tick(mars, ticks);
				} else {
					ticks -= pwm_tick(mars, 1);
				}
				mars->pwm_counter &= 0xFFF;
			} else {
				mars->pwm_counter = mars->regs[S32X_PWM_CYCLE];
				if (mars->pwm_counter == 1) {
					ticks -= pwm_tick(mars, ticks);
					mars->pwm_counter = 1;
				} else {
					ticks -= pwm_tick(mars, 1);
					mars->pwm_counter &= 0xFFF;
				}
			}
		}
	} else {
		while (ticks)
		{
			ticks -= pwm_tick(mars, ticks);
		}
	}
}

static void save_sh2_state(s32x *mars, sh2_context *sh2)
{
	sh2_context *dst = sh2->main ? mars->main_tmp : mars->sub_tmp;
	memcpy(dst->gpr, sh2->gpr, sizeof(sh2->gpr));
	dst->vbr = sh2->vbr;
	dst->sr = sh2->sr;
	dst->pr = sh2->pr;
	dst->pc = sh2->pc;
	dst->macl = sh2->macl;
	dst->mach = sh2->mach;
	dst->gbr = sh2->gbr;
	dst->prefetch_next = sh2->prefetch_next;
	dst->prefetch_cur = sh2->prefetch_cur;
	dst->t = sh2->t;
	dst->s = sh2->s;
	dst->q = sh2->q;
	dst->m = sh2->m;
	dst->delay_slot = sh2->delay_slot;
	mars->saved_sh2_state = 1;
}

static void maybe_restore_sh2(s32x *mars, sh2_context *sh2)
{
	if (mars->saved_sh2_state) {
		mars->saved_sh2_state = 0;
		sh2_context *src = sh2->main ? mars->main_tmp : mars->sub_tmp;
		memcpy(sh2->gpr, src->gpr, sizeof(sh2->gpr));
		sh2->vbr = src->vbr;
		sh2->sr = src->sr;
		sh2->pr = src->pr;
		sh2->pc = src->pc;
		sh2->macl = src->macl;
		sh2->mach = src->mach;
		sh2->gbr = src->gbr;
		sh2->prefetch_next = src->prefetch_next;
		sh2->prefetch_cur = src->prefetch_cur;
		sh2->t = src->t;
		sh2->s = src->s;
		sh2->q = src->q;
		sh2->m = src->m;
		sh2->delay_slot = src->delay_slot;
	}
}

void s32x_run(s32x *mars, uint32_t target)
{
	uint32_t sh2_target = target * 3;
	if (sh2_target > mars->main->cycles) {
		while (sh2_target > mars->main->cycles)
		{
			uint32_t cur_target;
			if (sh2_target - mars->main->cycles > MAX_SH2_CYCLES) {
				cur_target = mars->main->cycles + MAX_SH2_CYCLES;
			} else {
				cur_target = sh2_target;
			}
			mars->cur_sh2_target = cur_target;
#ifndef IS_LIB
			if (mars->main_enter_debugger && !mars->main->reset) {
				mars->main_enter_debugger = 0;
				if (mars->main->need_reset) {
					sh2_reset(mars->main);
				}
				sh2_debugger(mars->main);
			}
#endif
			sh2_run(mars->main, cur_target);
			maybe_restore_sh2(mars, mars->main);
#ifndef IS_LIB
			if (mars->sub_enter_debugger && !mars->sub->reset) {
				mars->sub_enter_debugger = 0;
				if (mars->sub->need_reset) {
					sh2_reset(mars->sub);
				}
				sh2_debugger(mars->sub);
			}
#endif
			sh2_run(mars->sub, cur_target);
			maybe_restore_sh2(mars, mars->sub);
			s32x_pwm_run(mars, cur_target);
		}
	}
	s32x_video_run(&mars->video, target);
}

void main_sh2_next_int(sh2_context *sh2)
{
	s32x *mars = sh2->system;
	uint32_t priority_mask = sh2->sr >> 4 & 0xF;
	sh2->int_cycle = 0xFFFFFFFF;
	sh2->int_priority = priority_mask;
	sh2->int_ack = NULL;
	if (priority_mask < 12) {
		uint32_t vint_cycle = 0xFFFFFFFF;
		if (mars->sh2_regs[S32X_SH2_INT_CTRL] & BIT_VERT_INT_EN) {
			if (mars->video.main_vint_pending) {
				vint_cycle = sh2->cycles;
			} else {
				vint_cycle = (mars->video.cycle + s32x_cycles_to_vblank(&mars->video)) * 3;
			}
		}
		if (vint_cycle < sh2->int_cycle) {
			sh2->int_cycle = vint_cycle;
			sh2->int_vector = 70;
			sh2->int_priority = 12;
		}
		if (priority_mask < 10) {
			uint32_t hint_cycle = 0xFFFFFFFF;
			if (mars->sh2_regs[S32X_SH2_INT_CTRL] & BIT_HORZ_INT_EN) {
				if (mars->video.main_hint_pending) {
					hint_cycle = sh2->cycles;
				} else {
					hint_cycle = (mars->video.cycle + s32x_cycles_to_hint(&mars->video)) * 3;
				}
			}
			if (hint_cycle < sh2->int_cycle) {
				sh2->int_cycle = hint_cycle;
				sh2->int_vector = 69;
				sh2->int_priority = 10;
			}
			if (priority_mask < 8) {
				uint32_t cmd_int_cycle = 0xFFFFFFFF;
				if ((mars->sh2_regs[S32X_SH2_INT_CTRL] & BIT_CMD_INT_EN) && (mars->regs[S32X_INT_CTRL] & BIT_MAIN_INT) ) {
					cmd_int_cycle = sh2->cycles;
				}
				if (cmd_int_cycle < sh2->int_cycle) {
					sh2->int_cycle = cmd_int_cycle;
					sh2->int_vector = 68;
					sh2->int_priority = 8;
				}
				if (priority_mask < 6) {
					uint32_t pwm_int_cycle = 0xFFFFFFFF;
					if (mars->sh2_regs[S32X_SH2_INT_CTRL] & BIT_PWM_INT_EN) {
						sh2_run(mars->sub, sh2->cycles);
						s32x_pwm_run(mars, sh2->cycles);
						if (mars->pwm_main_int_pending) {
							pwm_int_cycle = sh2->cycles;
						} else if (mars->pwm_counter != 1) {
							pwm_int_cycle = mars->pwm_cycle + 7 * ((mars->pwm_counter - 2) & 0xFFFF);
							pwm_int_cycle += ((mars->pwm_timer - 1) & 0xF) * ((mars->regs[S32X_PWM_CYCLE] - 2) & 0xFFFF) * 7;
						}
					}
					if (pwm_int_cycle < sh2->int_cycle) {
						sh2->int_cycle = pwm_int_cycle;
						sh2->int_vector = 67;
						sh2->int_priority = 6;
					}
				}
			}
		}
	}
	sh7095_next_int(sh2, priority_mask);
}

void sub_sh2_next_int(sh2_context *sh2)
{
	s32x *mars = sh2->system;
	uint32_t priority_mask = sh2->sr >> 4 & 0xF;
	sh2->int_cycle = 0xFFFFFFFF;
	sh2->int_priority = priority_mask;
	sh2->int_ack = NULL;
	if (priority_mask < 12) {
		uint32_t vint_cycle = 0xFFFFFFFF;
		if (mars->sh2_regs[S32X_SH2_SUB_INT] & BIT_VERT_INT_EN) {
			if (mars->video.sub_vint_pending) {
				vint_cycle = sh2->cycles;
			} else {
				vint_cycle = (mars->video.cycle + s32x_cycles_to_vblank(&mars->video)) * 3;
			}
		}
		if (vint_cycle < sh2->int_cycle) {
			sh2->int_cycle = vint_cycle;
			sh2->int_vector = 70;
			sh2->int_priority = 12;
		}
		if (priority_mask < 10) {
			uint32_t hint_cycle = 0xFFFFFFFF;
			if (mars->sh2_regs[S32X_SH2_SUB_INT] & BIT_HORZ_INT_EN) {
				if (mars->video.sub_hint_pending) {
					hint_cycle = sh2->cycles;
				} else {
					hint_cycle = (mars->video.cycle + s32x_cycles_to_hint(&mars->video)) * 3;
				}
			}
			if (hint_cycle < sh2->int_cycle) {
				sh2->int_cycle = hint_cycle;
				sh2->int_vector = 69;
				sh2->int_priority = 10;
			}
			if (priority_mask < 8) {
				uint32_t cmd_int_cycle = 0xFFFFFFFF;
				if ((mars->sh2_regs[S32X_SH2_SUB_INT] & BIT_CMD_INT_EN) && mars->regs[S32X_INT_CTRL] & BIT_SUB_INT) {
					cmd_int_cycle = sh2->cycles;
				}
				if (cmd_int_cycle < sh2->int_cycle) {
					sh2->int_cycle = cmd_int_cycle;
					sh2->int_vector = 68;
					sh2->int_priority = 8;
				}
				if (priority_mask < 6) {
					uint32_t pwm_int_cycle = 0xFFFFFFFF;
					if (mars->sh2_regs[S32X_SH2_SUB_INT] & BIT_PWM_INT_EN) {
						s32x_pwm_run(mars, sh2->cycles);
						if (mars->pwm_sub_int_pending) {
							pwm_int_cycle = sh2->cycles;
						} else if (mars->pwm_counter != 1) {
							pwm_int_cycle = mars->pwm_cycle + 7 * ((mars->pwm_counter - 2) & 0xFFFF);
							pwm_int_cycle += ((mars->pwm_timer - 1) & 0xF) * ((mars->regs[S32X_PWM_CYCLE] - 2) & 0xFFFF) * 7;
						}
					}
					if (pwm_int_cycle < sh2->int_cycle) {
						sh2->int_cycle =pwm_int_cycle;
						sh2->int_vector = 67;
						sh2->int_priority = 6;
					}
				}
			}
		}
	}
	sh7095_next_int(sh2, priority_mask);
}

void s32x_adjust_cycles(s32x *mars, uint32_t deduction)
{
	if (mars->video.cycle > deduction) {
		mars->video.cycle -= deduction;
	} else {
		mars->video.cycle = 0;
	}
	deduction *= 3;
	if (mars->main->cycles > deduction) {
		mars->main->cycles -= deduction;
	} else {
		mars->main->cycles = 0;
	}
	sh7095_adjust_cycles(mars->main, deduction);
	if (mars->sub->cycles > deduction) {
		mars->sub->cycles -= deduction;
	} else {
		mars->sub->cycles = 0;
	}
	sh7095_adjust_cycles(mars->sub, deduction);
	if (mars->pwm_cycle > deduction) {
		mars->pwm_cycle -= deduction;
	} else {
		mars->pwm_cycle = 0;
	}
	main_sh2_next_int(mars->main);
	sub_sh2_next_int(mars->sub);
}

void s32x_enable_scope(s32x *mars, oscilloscope *scope, uint32_t main_clock)
{
	mars->scope = scope;
	mars->scope_left = scope_add_channel(scope, "PWM Left", main_clock * 3 / (7 * PWM_DECIMATE));
	mars->scope_right = scope_add_channel(scope, "PWM Right", main_clock * 3 / (7 * PWM_DECIMATE));
}

void s32x_set_speed(s32x *mars, uint32_t main_clock)
{
	render_audio_adjust_clock(mars->pwm, main_clock * 3, 7 * PWM_DECIMATE);
}

uint16_t s32x_68k_read(uint32_t address, void *vcontext)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	s32x_run(mars, m68k->cycles);
	if (address < 0xA15100 + (S32X_NUM_REGS * 2)) {
		uint32_t reg = (address & 0xFE) >> 1;
		if (reg == S32X_PWM_WIDTH_M) {
			//TODO: test what happens when reading the FIFO status bits here when L & R don't match
			return mars->regs[S32X_PWM_WIDTH_L] & mars->regs[S32X_PWM_WIDTH_R];
		} else if (reg == S32X_DREQ_LEN) {
			//supposedly the low two bits are always 0 here
			//but it's convenient to use them to track trasnfer progress, so we just mask them here
			return mars->regs[S32X_DREQ_LEN] & 0xFFFC;
		}
		return mars->regs[reg];
	} else if (address >= 0xA15180) {
		//FM=1: the adapter completes the 68K cycle at once with no VDP access
		//(MiSTer IF.sv MD_VDP_SEL && ADCR.FM -> VDP_DTACK_N <= 0). The old
		//spin held the 68K for the whole SH-2 window on every VDP register
		//read made under FM (a rom that polls FS at 0xA1518A starves).
		if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM) {
			return 0xFFFF;
		}
		return s32x_video_68k_read(address, &mars->video);
	}
	return 0xFFFF;
}

uint8_t s32x_68k_read_b(uint32_t address, void *vcontext)
{
	uint16_t val = s32x_68k_read(address & ~1, vcontext);
	if (address & 1) {
		return val;
	}
	return val >> 8;
}

uint16_t s32x_sh2_read(uint32_t address, void *vcontext)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	if (sh2->main) {
		sh2_run(mars->sub, sh2->cycles);
	}
	if (address < 0x0004000 + (S32X_NUM_REGS * 2)) {
		uint32_t reg = (address & 0xFE) >> 1;
		switch (reg)
		{
		case S32X_SH2_INT_CTRL:
			if (sh2 != mars->main) {
				return (mars->sh2_regs[reg] & 0xFFF0) | mars->sh2_regs[S32X_SH2_SUB_INT];
			}
		case S32X_SH2_STANDBY:
		case S32X_SH2_HINT_COUNT:
			return mars->sh2_regs[reg];
		case S32X_DREQ_LEN:
			//supposedly the low two bits are always 0 here
			//but it's convenient to use them to track trasnfer progress, so we just mask them here
			return mars->regs[S32X_DREQ_LEN] & 0xFFFC;
		case S32X_DREQ_FIFO:
			//TODO: test what happens if you read from an empty FIFO
			//TODO: test what happens if you read from the FIFO with 68S=0
			fifostat[3]++;
			if (mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_68S) {
				if ((mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_FULL) || mars->dreq_fifo_write != mars->dreq_fifo_read) {
					uint16_t value = mars->dreq_fifo[mars->dreq_fifo_read++];
					if (trace_dreq) trace_dreq_row("read", sh2->main ? "shm" : "shs", value);
					mars->dreq_fifo_read &= 0x7;
					mars->regs[S32X_DREQ_CTRL] &= ~BIT_DREQ_FULL;
					mars->regs[S32X_DREQ_LEN]--;
					if (mars->dreq_fifo_write == mars->dreq_fifo_read) {
						//TODO: if/when edge vs level DREQ Is implemented
						//generate a new edge here when the fifo is NOT empty
						sh7095_clear_dreq0(mars->main);
						sh7095_clear_dreq0(mars->sub);
					}
					if (!mars->regs[S32X_DREQ_LEN]) {
						fifostat[7]++;
						if (trace_dreq) trace_dreq_row("end", sh2->main ? "shm" : "shs", 0);
						mars->regs[S32X_DREQ_CTRL] &= ~BIT_DREQ_68S;
					}
					return value;
				}
			}
			fifostat[4]++;
			return 0;
		case S32X_PWM_WIDTH_M:
			s32x_pwm_run(mars, sh2->cycles);
			//TODO: test what happens when reading the FIFO status bits here when L & R don't match
			return mars->regs[S32X_PWM_WIDTH_L] & mars->regs[S32X_PWM_WIDTH_R];
		case S32X_PWM_WIDTH_L:
		case S32X_PWM_WIDTH_R:
			s32x_pwm_run(mars, sh2->cycles);
		default:
			return mars->regs[reg];
		}
	} else if (address >= 0x0004100) {
		if (!(mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM)) {
			sh2->cycles = mars->cur_sh2_target;
			save_sh2_state(mars, sh2);
			return 0xFFFF;
		}
		s32x_video_run(&mars->video, sh2->cycles / 3);
		return s32x_video_sh2_read(address, &mars->video);
	}
	return 0xFFFF;
}

uint8_t s32x_sh2_read_b(uint32_t address, void *vcontext)
{
	uint16_t val = s32x_sh2_read(address & ~1, vcontext);
	if (address & 1) {
		return val;
	}
	return val >> 8;
}

//TODO: confirm which bits are actually writeable
static uint16_t reg_write_masks[S32X_NUM_REGS] = {
	0x8003,
	0x0003,
	0x0003,
	0x0007,
	0x00FF,
	0xFFFE,
	0x00FF,
	0xFFFF,
	0xFFFC,
	[S32X_SEGA_TV] = 0x0001,
	[S32X_COMM_0] = 0xFFFF, 0xFFFF,
	0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF,
	0xFFFF, 0xFFFF,
	0x000F,
	0x0FFF
};

/* CART-ROM ARBITER (mholzinger fork, 2026-09-23, env BLASTEM_BUS_ARB=1, default off).
 * MiSTer IF.sv ROM_ST (795-910): the 32X adapter serialises every cart access
 * from either CPU through one state machine; an SH-2 word takes RS_IDLE ->
 * RS_SH_WAIT -> RS_SH_READ -> RS_SH_END (~2 SH-2 clocks, burst words back to
 * back under one grant), an MD access RS_MD_RW -> RS_MD_READ -> RS_MD_END
 * (~3 SH-2 clocks + the board ROM wait), SH-2 first at RS_IDLE. The system
 * registers (COMM etc.) are NOT arbitrated (IF.sv 298/486: independent
 * always-blocks, no wait), and the VDP port is partitioned by FM. Upstream
 * BlastEm charges each CPU its own fixed cost and never lets one wait for
 * the other; with the knob on, a cart access from either CPU waits for the
 * other's access in flight. Times in MCLK (53.69 MHz): SH-2 cycles are
 * MCLK*3, 68K cycles are MCLK. */
#define ARB_SH_WORD_MCLK  5   /* ~2.1 SH-2 clocks incl. the board ROM wait */
#define ARB_MD_ACCESS_MCLK 8  /* ~3.4 SH-2 clocks */
static int arb_on = -1;
static uint32_t arb_rom_busy_until;   /* MCLK */
static int arb_last_side = -1;        /* 0 = 68K, 1 = SH-2: a CPU never waits on its own access (burst words share one grant, IF.sv RS_SH_CONT) */
static uint32_t arb_last_start;       /* MCLK the holder's access began: the CPUs run in slices, so an access stamped in the other's FUTURE must not be waited on */
uint64_t arbstat[6];                  /* [0] 68K cart accesses [1] 68K wait MCLK [2] SH-2 cart words [3] SH-2 wait MCLK [4] 68K accesses that waited [5] SH-2 words that waited */
static inline int arb_enabled(void)
{
	if (arb_on < 0) { const char *e = getenv("BLASTEM_BUS_ARB"); arb_on = e ? atoi(e) : 0; }
	return arb_on;
}
static inline uint32_t arb_take(uint32_t now_mclk, uint32_t occupancy, int side)
{
	uint32_t wait = 0;
	if ((int32_t)(arb_rom_busy_until - now_mclk) > 0) {
		if (arb_last_side != side) {
			if ((int32_t)(arb_last_start - now_mclk) <= 0) {
				/* the other CPU's access already began: wait for it to finish */
				wait = arb_rom_busy_until - now_mclk;
				arbstat[side ? 5 : 4]++;
			} else {
				/* it lies in our future (slice skew): we go first, it will not see us */
				arb_rom_busy_until = now_mclk;
			}
		} else {
			/* same CPU, grant still held: the new word queues behind its own burst */
			now_mclk = arb_rom_busy_until;
		}
	}
	arbstat[side ? 3 : 1] += wait;
	arbstat[side ? 2 : 0]++;
	arb_last_start = now_mclk + wait;
	arb_rom_busy_until = arb_last_start + occupancy;
	arb_last_side = side;
	return wait;
}
static uint8_t *arb_cart;             /* gen->cart as bytes (bus order words) */
static uint32_t arb_cart_mask;
static uint8_t *arb_bank_ptr;         /* 0x900000 window base when mapped high */
uint16_t arb_68k_fixed_read_w(uint32_t address, void *vcontext)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	if (!(mars->regs[S32X_ADAPT_CTRL] & BIT_ADEN_M68K) || (mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_RV) || !arb_cart) {
		return 0xFFFF;
	}
	m68k->cycles += arb_take(m68k->cycles, ARB_MD_ACCESS_MCLK, 0);
	return *(uint16_t *)(arb_cart + ((address & 0x7FFFF) & arb_cart_mask));
}
uint8_t arb_68k_fixed_read_b(uint32_t address, void *vcontext)
{
	uint16_t v = arb_68k_fixed_read_w(address & ~1, vcontext);
	return (address & 1) ? v : v >> 8;
}
uint16_t arb_68k_bank_read_w(uint32_t address, void *vcontext)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	if (!(mars->regs[S32X_ADAPT_CTRL] & BIT_ADEN_M68K) || (mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_RV) || !arb_bank_ptr) {
		return 0xFFFF;
	}
	m68k->cycles += arb_take(m68k->cycles, ARB_MD_ACCESS_MCLK, 0);
	return *(uint16_t *)(arb_bank_ptr + (address & 0xFFFFF));
}
uint8_t arb_68k_bank_read_b(uint32_t address, void *vcontext)
{
	uint16_t v = arb_68k_bank_read_w(address & ~1, vcontext);
	return (address & 1) ? v : v >> 8;
}
static uint16_t arb_sh2_rom_read_w(uint32_t offset, void *vcontext)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	uint32_t now = sh2->cycles / 3;
	sh2->cycles += 3 * arb_take(now, ARB_SH_WORD_MCLK, 1);
	return *(uint16_t *)(((uint8_t *)mars->rom) + offset);
}
static uint8_t arb_sh2_rom_read_b(uint32_t offset, void *vcontext)
{
	uint16_t v = arb_sh2_rom_read_w(offset & ~1, vcontext);
	return (offset & 1) ? v : v >> 8;
}

static void check_cart_map_change(uint32_t reg, m68k_context *m68k, uint16_t changes)
{
	uint8_t aden_changed = reg == S32X_ADAPT_CTRL && (changes & BIT_ADEN_M68K);
	uint8_t rv_changed = reg == S32X_DREQ_CTRL && (changes & BIT_DREQ_RV);
	uint8_t bank_changed = reg == S32X_CART_BANK && (changes & S32X_BANK_MASK);
	if (aden_changed || rv_changed || bank_changed) {
		genesis_context *gen = m68k->system;
		s32x *mars = gen->mars;
		uint8_t cart_mapped_high = (mars->regs[S32X_ADAPT_CTRL] & BIT_ADEN_M68K) && !(mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_RV);
		if (cart_mapped_high) {
			mars->main->mem_pointers[0] = arb_enabled() ? NULL : (uint8_t *)gen->cart;
			mars->sub->mem_pointers[0] = arb_enabled() ? NULL : (uint8_t *)gen->cart;
			m68k->mem_pointers[0] = NULL;
			m68k->mem_pointers[1] = arb_enabled() ? NULL : gen->cart;
			arb_cart = (uint8_t *)gen->cart;
			// This is either for SRAM with the cart mapped low or unused
			m68k->mem_pointers[3] = NULL;
			uint32_t bank_start = (mars->regs[S32X_CART_BANK] & S32X_BANK_MASK) << 20;
			const memmap_chunk *chunk = find_map_chunk(gen->save_type == SAVE_I2C ? bank_start + 2 : bank_start, &m68k->opts->gen, 0, NULL);
			if (!chunk) {
				m68k->mem_pointers[2] = NULL;
				return;
			}
			uint32_t offset = bank_start - (chunk->start & ~chunk->mask);
			offset &= chunk->mask;
			if (chunk->flags & (MMAP_ONLY_ODD | MMAP_ONLY_EVEN)) {
				offset >>= 1;
			}
			if (gen->mapper_type == MAPPER_SEGA_SRAM && chunk->write_16 == s32x_write_sram_area_w && (gen->bank_regs[0] & 3) == 1) {
				gen->mapper_temp = ((uint8_t *)chunk->buffer) + offset;
				m68k->mem_pointers[2] = NULL;
			} else {
				arb_bank_ptr = ((uint8_t *)chunk->buffer) + offset;
				m68k->mem_pointers[2] = arb_enabled() ? NULL : (uint16_t *)(((uint8_t *)chunk->buffer) + offset);
				gen->mapper_temp = NULL;
			}
		} else {
			m68k->mem_pointers[0] = gen->cart;
			m68k->mem_pointers[1] = NULL;
			m68k->mem_pointers[2] = NULL;
			memmap_chunk *chunk = NULL;
			for (uint32_t i = 0; i < m68k->opts->gen.memmap_chunks; i++)
			{
				const memmap_chunk *chunk = m68k->opts->gen.memmap + i;
				if ((chunk->flags & MMAP_PTR_IDX) && chunk->ptr_index == 3) {
					m68k->mem_pointers[3] = chunk->buffer;
					break;
				} else {
					chunk = NULL;
				}
			}
			if (gen->mapper_type == MAPPER_SEGA_SRAM) {
				if ((gen->bank_regs[0] & 3) == 1) {
					m68k->mem_pointers[3] = NULL;
					if (chunk) {
						gen->mapper_temp = chunk->buffer;
					}
				} else {
					if (chunk) {
						m68k->mem_pointers[3] = chunk->buffer;
					}
					gen->mapper_temp = NULL;
				}
			} else if (chunk) {
				m68k->mem_pointers[3] = chunk->buffer;
			}
		}
		if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADEN_M68K) {
			m68k->mem_pointers[9] = mars->vector_rom;
		} else {
			m68k->mem_pointers[9] = gen->cart;
		}
		if (aden_changed) {
			m68k_invalidate_code_range(m68k, 0x0, 0x100);
		}
		if (bank_changed) {
			m68k_invalidate_code_range(m68k, 0x900000, 0xA00000);
		}
		gen_update_z80_bank_pointer(gen);
	}
}

static void maybe_update_pwm_dreq(s32x *mars)
{
	if (!(mars->regs[S32X_PWM_CTRL] & BIT_PWM_RTP)) {
		return;
	}
	uint8_t data_needed = 1;
	switch (mars->regs[S32X_PWM_CTRL] & 3)
	{
	case 1: data_needed = !(mars->regs[S32X_PWM_WIDTH_L] & BIT_PWM_FULL); break;
	case 2: data_needed = !(mars->regs[S32X_PWM_WIDTH_R] & BIT_PWM_FULL); break;
	//TODO: what happens if the illegal 3 value is used
	case 3: data_needed = 0; break;
	}
	switch (mars->regs[S32X_PWM_CTRL] >> 2 & 3)
	{
	case 1: data_needed = data_needed && !(mars->regs[S32X_PWM_WIDTH_R] & BIT_PWM_FULL); break;
	case 2: data_needed = data_needed && !(mars->regs[S32X_PWM_WIDTH_L] & BIT_PWM_FULL); break;
	//TODO: what happens if the illegal 3 value is used
	case 3: data_needed = 0; break;
	}
	if (data_needed) {
		sh7095_assert_dreq1(mars->main);
		sh7095_assert_dreq1(mars->sub);
	} else {
		sh7095_clear_dreq1(mars->main);
		sh7095_clear_dreq1(mars->sub);
	}
}


void s32x_68k_sysreg_write(uint32_t reg, m68k_context *m68k, s32x *mars, uint16_t mask, uint16_t value)
{
	uint16_t old = mars->regs[reg];
	uint16_t new = (old & ~mask) | (value & mask);
	uint16_t changes = old ^ new;
	switch(reg)
	{
	case S32X_ADAPT_CTRL:
		if (changes & BIT_SH2_RESET) {
			if (new & BIT_SH2_RESET) {
				sh2_clear_reset(mars->main);
				sh2_clear_reset(mars->sub);
			} else {
				sh2_assert_reset(mars->main);
				sh2_assert_reset(mars->sub);
			}
		}
		if (changes & BIT_ADEN_M68K) {
			if (new & BIT_ADEN_M68K) {
				mars->sh2_regs[S32X_SH2_INT_CTRL] |= BIT_ADEN_SH2;
			} else {
				mars->sh2_regs[S32X_SH2_INT_CTRL] &= ~BIT_ADEN_SH2;
			}
		}
		if (changes & BIT_ADCT_FM) {
			if (new & BIT_ADCT_FM) fbxstat[2]++; else fbxstat[5]++;
			mars->sh2_regs[S32X_SH2_INT_CTRL] &= ~BIT_ADCT_FM;
			mars->sh2_regs[S32X_SH2_INT_CTRL] |= new & BIT_ADCT_FM;
		}
		break;
	case S32X_INT_CTRL:
		if (changes & BIT_MAIN_INT) {
			main_sh2_next_int(mars->main);
		}
		if (changes & BIT_SUB_INT) {
			sub_sh2_next_int(mars->sub);
		}
		break;
	case S32X_DREQ_CTRL:
		//RV changes handled below
		if (changes & BIT_DREQ_68S) {
			if (trace_dreq) trace_dreq_row((new & BIT_DREQ_68S) ? "start" : "end", "m68k", (new & BIT_DREQ_68S) ? mars->regs[S32X_DREQ_LEN] : 0);
			if (old & BIT_DREQ_68S) {
				fifostat[6]++;
				//unclear if FIFO is emptied, or if the full bit is just suppressed
				new &= ~BIT_DREQ_FULL;
				mars->dreq_fifo_write = mars->dreq_fifo_read = 0;
				sh7095_clear_dreq0(mars->main);
				sh7095_clear_dreq0(mars->sub);
			} else if (((mars->dreq_fifo_write - mars->dreq_fifo_read) & 0x7) >= 4) {
				sh7095_assert_dreq0(mars->main);
				sh7095_assert_dreq0(mars->sub);
			}
			if (!(old & BIT_DREQ_68S)) fifostat[5]++;
		}
		break;
	case S32X_DREQ_LEN:	
		//force low bits to 0 on write
		new &= 0xFFFC;
		break;
	case S32X_DREQ_FIFO:
		//TODO: test what happens when you write to a full FIFO
		//TODO: test what happens if you write to this when 68S is 0
		fifostat[0]++;
		if (!(mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_68S)) fifostat[2]++;
		if (trace_dreq) trace_dreq_row((mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_68S) ? "push" : "miss", "m68k", value);
		if (mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_68S) {
			mars->dreq_fifo[mars->dreq_fifo_write++] = value;
			mars->dreq_fifo_write &= 0x7;
			if (mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_FULL) {
				//treating this like the PWM FIFO and evicting the oldest word for now
				fifostat[1]++;
				if (trace_dreq) trace_dreq_row("miss", "m68k", mars->dreq_fifo[mars->dreq_fifo_read]);
				mars->dreq_fifo_read++;
				mars->dreq_fifo_read &= 0x7;
				
			} else if (mars->dreq_fifo_write == mars->dreq_fifo_read) {
				mars->regs[S32X_DREQ_CTRL] |= BIT_DREQ_FULL;
			}
			if ((mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_68S)
				&& ((mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_FULL) || ((mars->dreq_fifo_write - mars->dreq_fifo_read) & 0x7) >= 4)
			) {
				sh7095_assert_dreq0(mars->main);
				sh7095_assert_dreq0(mars->sub);
			}
		}
		break;
	case S32X_PWM_WIDTH_M:
	case S32X_PWM_WIDTH_L:
		pwm_fifo_write(&mars->fifo_left, &mars->regs[S32X_PWM_WIDTH_L], value);
		if (reg != S32X_PWM_WIDTH_M) {
			maybe_update_pwm_dreq(mars);
			return;
		}
	case S32X_PWM_WIDTH_R:
		pwm_fifo_write(&mars->fifo_right, &mars->regs[S32X_PWM_WIDTH_R], value);
		maybe_update_pwm_dreq(mars);
		return;
	}
	if (trace_comm && reg >= S32X_COMM_0 && reg <= S32X_COMM_7) trace_comm_row("m68k", reg - S32X_COMM_0, new);
	mars->regs[reg] = new;
	check_cart_map_change(reg, m68k, changes);
}

void *s32x_68k_write(uint32_t address, void *vcontext, uint16_t value)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	s32x_run(mars, m68k->cycles);
	if (address < 0xA15100 + (S32X_NUM_REGS * 2)) {
		uint32_t reg = (address & 0xFF) >> 1;
		uint16_t mask = reg_write_masks[reg];
		dprintf("32X 68K Write: %06X: %04X\n", address, value);
		s32x_68k_sysreg_write(reg, m68k, mars, mask, value);
	} else if (address >= 0xA15180) {
		if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM) {
			//writes are ignored when FM is set
			return vcontext;
		}
		gen->bus_busy = 1;
		s32x_trace_src = "m68k";
		for (;;)
		{
			s32x_run(mars, m68k->cycles);
			uint32_t wait_cycles = s32x_video_68k_write(address, &mars->video, value);
			if (wait_cycles) {
				uint32_t target = m68k->cycles + wait_cycles;
				if (target > m68k->sync_cycle) {
					if (m68k->sync_cycle <= m68k->cycles) {
						target = m68k->sync_cycle + 1;
					} else {
						target = m68k->sync_cycle;
					}
				}
				m68k->cycles = target;
#ifdef NEW_CORE
				m68k->sync_components(m68k, 0);
#else
				m68k->opts->sync_components(m68k, 0);
#endif
			} else {
				break;
			}
		}
		gen->bus_busy = 0;
	}
	return vcontext;
}

void *s32x_68k_write_b(uint32_t address, void *vcontext, uint8_t value)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	s32x_run(mars, m68k->cycles);
	if (address < 0xA15100 + (S32X_NUM_REGS * 2)) {
		dprintf("32X 68K Write (byte): %06X: %02X\n", address, value);
		uint32_t reg = (address & 0xFF) >> 1;
		uint16_t mask = reg_write_masks[reg];
		uint16_t extended;
		if (address & 1) {
			extended = value;
			mask &= 0x00FF;;
		} else {
			extended = value << 8;
			mask &= 0xFF00;
		}
		s32x_68k_sysreg_write(reg, m68k, mars, mask, extended);
	} else if (address >= 0xA15180) {
		if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM) {
			//writes are ignored when FM is set
			return vcontext;
		}
		gen->bus_busy = 1;
		for (;;)
		{
			s32x_run(mars, m68k->cycles);
			uint32_t wait_cycles = s32x_video_68k_write_b(address, &mars->video, value);
			if (wait_cycles) {
				uint32_t target = m68k->cycles + wait_cycles;
				if (target > m68k->sync_cycle) {
					if (m68k->sync_cycle <= m68k->cycles) {
						target = m68k->sync_cycle + 1;
					} else {
						target = m68k->sync_cycle;
					}
				}
				m68k->cycles = target;
#ifdef NEW_CORE
				m68k->sync_components(m68k, 0);
#else
				m68k->opts->sync_components(m68k, 0);
#endif
			} else {
				break;
			}
		}
		gen->bus_busy = 0;
	}
	return vcontext;
}

//TODO: confirm which bits are actually writeable
static uint16_t sh2_write_masks[S32X_NUM_REGS] = {
	0x808F, //0 = interrupt mask
	0xFFFF, //2 = stand by change
	0x00FF, //4 = h count
	[S32X_SEGA_TV] = 0x0001,
	[S32X_COMM_0] = 0xFFFF, 0xFFFF,
	0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF,
	0xFFFF, 0xFFFF,
	0x0F8F,
	0x0FFF
};

static void s32x_sh2_sysreg_write(uint32_t reg, sh2_context *sh2, s32x *mars, uint16_t mask, uint16_t value)
{
	uint16_t *base = reg < S32X_NUM_SH2_REGS ? mars->sh2_regs : mars->regs;
	uint16_t old = base[reg];
	uint16_t new = (old & ~mask) | (value & mask);
	uint16_t changes = old ^ new;
	switch (reg)
	{
	case S32X_SH2_INT_CTRL:
		if (changes & BIT_ADCT_FM) {
			if (new & BIT_ADCT_FM) fbxstat[3]++; else fbxstat[4]++;
			mars->regs[S32X_ADAPT_CTRL] &= ~BIT_ADCT_FM;
			mars->regs[S32X_ADAPT_CTRL] |= new & BIT_ADCT_FM;
		}
		s32x_video_run(&mars->video, sh2->cycles / 3);
		mars->video.hen = (new & BIT_INTMASK_HEN) ? 1 : 0;
		if (sh2->main) {
			if (changes & S32X_INTEN_MASK) {
				base[reg] = new;
				main_sh2_next_int(sh2);
				if (changes & BIT_INTMASK_HEN) {
					sub_sh2_next_int(mars->sub);
				}
			}
		} else {
			uint16_t old_int = mars->sh2_regs[S32X_SH2_SUB_INT];
			uint16_t mask_int = mask & 0xF;
			uint16_t new_int = (old_int & ~mask_int) | (value & mask_int);
			changes = (old_int ^ new_int) | (changes & BIT_INTMASK_HEN);
			if (changes) {
				mars->sh2_regs[S32X_SH2_SUB_INT] = new_int;
				sub_sh2_next_int(sh2);
				if (changes & BIT_INTMASK_HEN) {
					main_sh2_next_int(mars->main);
				}
			}
			mask &= 0xFFF0;
			new = (old & ~mask) | (value & mask);
		}
		break;
	case S32X_SH2_HINT_COUNT:
		s32x_video_run(&mars->video, sh2->cycles / 3);
		mars->video.hint_count = new;
		main_sh2_next_int(mars->main);
		sub_sh2_next_int(mars->sub);
		break;
	case S32X_VINT_CLR:
		s32x_video_run(&mars->video, sh2->cycles / 3);
		if (sh2->main) {
			mars->video.main_vint_pending = 0;
			main_sh2_next_int(sh2);
		} else {
			mars->video.sub_vint_pending = 0;
			sub_sh2_next_int(sh2);
		}
		break;
	case S32X_HINT_CLR:
		s32x_video_run(&mars->video, sh2->cycles / 3);
		if (sh2->main) {
			mars->video.main_hint_pending = 0;
			main_sh2_next_int(sh2);
		} else {
			mars->video.sub_hint_pending = 0;
			sub_sh2_next_int(sh2);
		}
		break;
	case S32X_CMD_INT_CLR:
		if (sh2->main) {
			mars->regs[S32X_INT_CTRL] &= ~BIT_MAIN_INT;
			main_sh2_next_int(sh2);
		} else {
			mars->regs[S32X_INT_CTRL] &= ~BIT_SUB_INT;
			sub_sh2_next_int(sh2);
		}
		break;
	case S32X_PWM_INT_CLR:
		s32x_pwm_run(mars, sh2->cycles);
		if (sh2->main) {
			mars->pwm_main_int_pending = 0;
			main_sh2_next_int(sh2);
		} else {
			mars->pwm_sub_int_pending = 0;
			sub_sh2_next_int(sh2);
		}
		break;
	case S32X_PWM_WIDTH_M:
	case S32X_PWM_WIDTH_L:
		s32x_pwm_run(mars, sh2->cycles);
		pwm_fifo_write(&mars->fifo_left, &base[S32X_PWM_WIDTH_L], value);
		if (reg != S32X_PWM_WIDTH_M) {
			maybe_update_pwm_dreq(mars);
			return;
		}
	case S32X_PWM_WIDTH_R:
		s32x_pwm_run(mars, sh2->cycles);
		pwm_fifo_write(&mars->fifo_right, &base[S32X_PWM_WIDTH_R], value);
		maybe_update_pwm_dreq(mars);
		return;
	case S32X_PWM_CTRL:
		s32x_pwm_run(mars, sh2->cycles);
		if (changes & BIT_PWM_RTP) {
			if (new & BIT_PWM_RTP) {
				base[reg] = new;
				maybe_update_pwm_dreq(mars);
			} else {
				sh7095_clear_dreq1(mars->main);
				sh7095_clear_dreq1(mars->sub);
			}
		}
		break;
	case S32X_PWM_CYCLE:
		s32x_pwm_run(mars, sh2->cycles);
		break;
	}
	if (trace_comm && reg >= S32X_COMM_0 && reg <= S32X_COMM_7) trace_comm_row(sh2->main ? "shm" : "shs", reg - S32X_COMM_0, new);
	base[reg] = new;
}

void *s32x_sh2_write(uint32_t address, void *vcontext, uint16_t value)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	if (address < 0x0004000 + (S32X_NUM_REGS * 2)) {
		if (sh2->main) {
			sh2_run(mars->sub, sh2->cycles);
		}
		sh2->cycles += 3 * sh2->opts->gen.clock_divider;
		uint32_t reg = (address & 0xFE) >> 1;
		uint16_t mask = sh2_write_masks[reg];
		dprintf("32X SH2 %c Write: %06X: %04X\n", sh2 == mars->main ? 'M' : 'S', address, value);
		s32x_sh2_sysreg_write(reg, sh2, mars, mask, value);
	} else if (address >= 0x0004100) {
		//SH2 writes seem to always go through for some reason, even when FM is clear
		//have occasionally seen the writes be delayed, but not consistent
		//needs more testing
		sh2->cycles += 6 * sh2->opts->gen.clock_divider;
		s32x_trace_src = sh2->main ? "shm" : "shs";
		for (;;)
		{
			if (sh2->main) {
				sh2_run(mars->sub, sh2->cycles);
			}
			s32x_video_run(&mars->video, sh2->cycles / 3);
			uint32_t wait_cycles = s32x_video_sh2_write(address, &mars->video, value);
			if (wait_cycles) {
				//TODO: sync components
				sh2->cycles += wait_cycles;
			} else {
				break;
			}
		}
	}
	return vcontext;
}

void *s32x_sh2_write_b(uint32_t address, void *vcontext, uint8_t value)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	if (sh2->main) {
		sh2_run(mars->sub, sh2->cycles);
	}
	if (address < 0x0004000 + (S32X_NUM_REGS * 2)) {
		uint32_t reg = (address & 0xFE) >> 1;
		uint16_t mask = sh2_write_masks[reg];
		uint16_t extended;
		if (sh2->main) {
			sh2_run(mars->sub, sh2->cycles);
		}
		sh2->cycles += 3 * sh2->opts->gen.clock_divider;
		if (address & 1) {
			extended = value;
			mask &= 0x00FF;;
		} else {
			extended = value << 8;
			mask &= 0xFF00;
		}
		dprintf("32X SH2 Write: %06X: %04X\n", address, value);
		s32x_sh2_sysreg_write(reg, sh2, mars, mask, extended);
	} else if (address >= 0x0004100) {
		//SH2 writes seem to always go through for some reason, even when FM is clear
		//have occasionally seen the writes be delayed, but not consistent
		//needs more testing
		sh2->cycles += 6 * sh2->opts->gen.clock_divider;
		for (;;)
		{
			if (sh2->main) {
				sh2_run(mars->sub, sh2->cycles);
			}
			s32x_video_run(&mars->video, sh2->cycles / 3);
			uint32_t wait_cycles = s32x_video_sh2_write_b(address, &mars->video, value);
			if (wait_cycles) {
				//TODO: sync components
				sh2->cycles += wait_cycles;
			} else {
				break;
			}
		}
	}
	return vcontext;
}

static uint16_t *get_68K_vector_rom(uint32_t size)
{
	if (size < 0x100) {
		size = 0x100;
	}
	uint16_t *ret = calloc(1, size);
	char *m68k_path = tern_find_path_default(config, "system\0s32x_68k_bios\0", (tern_val){.ptrval = "32X_G_BIOS.bin"}, TVAL_PTR).ptrval;
	FILE *f = fopen(m68k_path, "rb");
	if (f) {
		fread(ret, 1, 0x100, f);
		byteswap_rom(0x100, ret);
		fclose(f);
	} else {
		warning("32X 68K BIOS not found at %s. Some games may function without it, but it is needed for full compatibility\n", m68k_path);
		ret[0] = ret[1] = 0;
		uint32_t vector = 0x880200;
		for (int i = 0; i < 47; i++)
		{
			ret[i * 2] = vector >> 16;
			ret[i * 2 + 1] = vector;
			vector += 6;
		}
		//TODO: fake the subroutines maybe?
	}
	for (uint32_t i = 0x100; i < size - 0xFF; i += 0x100)
	{
		memcpy(ret + i / 2, ret, 0x100);
	}
	return ret;
}

void *s32x_write_hint(uint32_t address, void *vcontext, uint16_t value)
{
	if (address >= 0x70 && address < 0x74) {
		m68k_context *m68k = vcontext;
		genesis_context *gen = m68k->system;
		s32x *mars = gen->mars;
		uint8_t cart_mapped_high = (mars->regs[S32X_ADAPT_CTRL] & BIT_ADEN_M68K) && !(mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_RV);
		if (cart_mapped_high) {
			mars->vector_rom[address >> 1] = value;
		}
	}
	return vcontext;
}

void *s32x_write_hint_b(uint32_t address, void *vcontext, uint8_t value)
{
	if (address >= 0x70 && address < 0x74) {
		m68k_context *m68k = vcontext;
		genesis_context *gen = m68k->system;
		s32x *mars = gen->mars;
		uint8_t cart_mapped_high = (mars->regs[S32X_ADAPT_CTRL] & BIT_ADEN_M68K) && !(mars->regs[S32X_DREQ_CTRL] & BIT_DREQ_RV);
		if (cart_mapped_high) {
			if (address & 1) {
				mars->vector_rom[address >> 1] &= 0xFF00;
				mars->vector_rom[address >> 1] |= value;
			} else {
				mars->vector_rom[address >> 1] &= 0x00FF;
				mars->vector_rom[address >> 1] |= value << 8;
			}
		}
	}
	return vcontext;
}

void *s32x_fb_write_w(uint32_t address, void *vcontext, uint16_t value)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	s32x_run(mars, m68k->cycles);
	fbxstat[0]++;
	if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM) {
		//TODO: confirm that this actually behaves like register writes
		fbxstat[1]++;
		return vcontext;
	}
	s32x_video_fb_write_w(address, &mars->video, value);
	return vcontext;
}

void *s32x_fb_write_b(uint32_t address, void *vcontext, uint8_t value)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	s32x_run(mars, m68k->cycles);
	fbxstat[6]++;
	if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM) {
		//TODO: confirm that this actually behaves like register writes
		fbxstat[7]++;
		return vcontext;
	}
	//byte writes behave as if they were written to the overwrite area
	s32x_video_overwrite_write_b(address, &mars->video, value);
	return vcontext;
}

uint16_t s32x_fb_read_w(uint32_t address, void *vcontext)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	s32x_run(mars, m68k->cycles);
	//FM=1: the adapter completes the 68K cycle at once with no VDP access
	//(MiSTer IF.sv: MD_VDP_SEL && ADCR.FM -> VDP_DTACK_N <= 0; ares returns
	//open bus). Stalling here until FM drops held the 68K for whole SH-2
	//windows and froze the game on roms that read the FB under FM.
	if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM) {
		return 0xFFFF;
	}
	return s32x_video_fb_read_w(address, &mars->video);
}

uint8_t s32x_fb_read_b(uint32_t address, void *vcontext)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	s32x_run(mars, m68k->cycles);
	if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM) {
		return 0xFF;
	}
	return s32x_video_fb_read_b(address, &mars->video);
}


/* Calibration knob (mholzinger fork, 2026-09-23): SH-2 clocks charged per
 * 16-bit framebuffer write by either SH-2. Upstream charges nothing; ares
 * charges ~6.8/word (13.6 a longword, LOOP.md 20); the FPGA measured ~1.6x
 * ares on the same rom. Env BLASTEM_FB_WAIT, default 0 = upstream. */
static int32_t fb_wait_clocks = -1;
static inline void charge_fb_write(sh2_context *sh2)
{
	if (fb_wait_clocks < 0) {
		const char *e = getenv("BLASTEM_FB_WAIT");
		fb_wait_clocks = e ? atoi(e) : 0;
	}
	sh2->cycles += fb_wait_clocks * sh2->opts->gen.clock_divider;
}
void *s32x_sh2_fb_write_w(uint32_t address, void *vcontext, uint16_t value)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	if (sh2->main) {
		sh2_run(mars->sub, sh2->cycles);
	}
	if (!(mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM)) {
		sh2->cycles = mars->cur_sh2_target;
		save_sh2_state(mars, sh2);
		return vcontext;
	}
	s32x_video_run(&mars->video, sh2->cycles / 3);
	charge_fb_write(sh2);
	s32x_video_fb_write_w(address, &mars->video, value);
	return vcontext;
}

void *s32x_sh2_fb_write_b(uint32_t address, void *vcontext, uint8_t value)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	if (sh2->main) {
		sh2_run(mars->sub, sh2->cycles);
	}
	if (!(mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM)) {
		sh2->cycles = mars->cur_sh2_target;
		save_sh2_state(mars, sh2);
		return vcontext;
	}
	s32x_video_run(&mars->video, sh2->cycles / 3);
	//byte writes behave as if they were written to the overwrite area
	charge_fb_write(sh2);
	s32x_video_overwrite_write_b(address, &mars->video, value);
	return vcontext;
}

uint16_t s32x_sh2_fb_read_w(uint32_t address, void *vcontext)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	if (sh2->main) {
		sh2_run(mars->sub, sh2->cycles);
	}
	if (!(mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM)) {
		sh2->cycles = mars->cur_sh2_target;
		save_sh2_state(mars, sh2);
		return 0xFFFF;
	}
	s32x_video_run(&mars->video, sh2->cycles / 3);
	return s32x_video_fb_read_w(address, &mars->video);
}

uint8_t s32x_sh2_fb_read_b(uint32_t address, void *vcontext)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	if (sh2->main) {
		sh2_run(mars->sub, sh2->cycles);
	}
	if (!(mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM)) {
		sh2->cycles = mars->cur_sh2_target;
		save_sh2_state(mars, sh2);
		return 0xFF;
	}
	s32x_video_run(&mars->video, sh2->cycles / 3);
	return s32x_video_fb_read_b(address, &mars->video);
}

void *s32x_overwrite_write_w(uint32_t address, void *vcontext, uint16_t value)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	s32x_run(mars, m68k->cycles);
	//FM=1: cycle completes at once, no VDP access (IF.sv); never stall the 68K here
	if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM) {
		return vcontext;
	}
	s32x_video_overwrite_write_w(address, &mars->video, value);
	return vcontext;
}

void *s32x_overwrite_write_b(uint32_t address, void *vcontext, uint8_t value)
{
	m68k_context *m68k = vcontext;
	genesis_context *gen = m68k->system;
	s32x *mars = gen->mars;
	s32x_run(mars, m68k->cycles);
	//FM=1: cycle completes at once, no VDP access (IF.sv); never stall the 68K here
	if (mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM) {
		return vcontext;
	}
	s32x_video_overwrite_write_b(address, &mars->video, value);
	return vcontext;
}

void *s32x_sh2_overwrite_write_w(uint32_t address, void *vcontext, uint16_t value)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	if (sh2->main) {
		sh2_run(mars->sub, sh2->cycles);
	}
	if (!(mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM)) {
		sh2->cycles = mars->cur_sh2_target;
		save_sh2_state(mars, sh2);
		return vcontext;
	}
	s32x_video_run(&mars->video, sh2->cycles / 3);
	charge_fb_write(sh2);
	s32x_video_overwrite_write_w(address, &mars->video, value);
	return vcontext;
}

void *s32x_sh2_overwrite_write_b(uint32_t address, void *vcontext, uint8_t value)
{
	sh2_context *sh2 = vcontext;
	s32x *mars = sh2->system;
	if (sh2->main) {
		sh2_run(mars->sub, sh2->cycles);
	}
	if (!(mars->regs[S32X_ADAPT_CTRL] & BIT_ADCT_FM)) {
		sh2->cycles = mars->cur_sh2_target;
		save_sh2_state(mars, sh2);
		return vcontext;
	}
	s32x_video_run(&mars->video, sh2->cycles / 3);
	charge_fb_write(sh2);
	s32x_video_overwrite_write_b(address, &mars->video, value);
	return vcontext;
}

uint32_t s32x_sh2_read_external_32(uint32_t address, sh2_context *sh2)
{
	address &= 0x7FFFFFF;
	uint32_t ret;
	if (address >= 0x6000000 && address < 0x6040000) {
		//SDRAM access always does a 16-byte burst, but a single burst can
		//satisfy both words of the longword read
		address &= 0x3FFFF;
		address >>= 1;
		s32x *mars = sh2->system;
		ret = mars->sdram[address] << 16;
		ret |= mars->sdram[address | 1] ;
		sh2->cycles += 10 * sh2->opts->gen.clock_divider;
	} else {
		ret = sh2->read16[1](address, sh2) << 16;
		ret |= sh2->read16[1](address | 2, sh2);
	}
	return ret;
}

void s32x_sh2_write_external_32(uint32_t address, sh2_context *sh2, uint32_t value)
{
	address &= 0x7FFFFFF;
	if (address >= 0x6000000 && address < 0x6040000) {
		//this also seems optimized for the 32-bit case despite the 16-bit bus
		address &= 0x3FFFF;
		address >>= 1;
		s32x *mars = sh2->system;
		mars->sdram[address] = value >> 16;
		mars->sdram[address | 1] = value;
		//this seems too fast, but I get way too low values on 32xspd.32x otherwise
		sh2->cycles += sh2->opts->gen.clock_divider;
	} else {
		sh2->write16[1](address, sh2, value >> 16);
		sh2->write16[1](address | 2, sh2, value);
	}
}

//TODO: share these with genesis.c
#define MCLKS_NTSC 53693175
#define MCLKS_PAL  53203395

s32x *alloc_32x(system_media *media, uint8_t pal, uint8_t cd_boot)
{
	static const memmap_chunk base_sh2_map[] = {
		{0x6000000, 0x6040000, .mask = 0x3FFFF, .flags = MMAP_READ | MMAP_WRITE | MMAP_CODE,
			//should be a 12-cycle burst, but I need 10 to get close to the right results in 32xspd.32x
			.read_cycles = 10, .write_cycles = 1, .burst_cycles = 10},
		{0x4000000, 0x4020000, .mask = 0x7FFFFFF, .read_16 = s32x_sh2_fb_read_w, .write_16 = s32x_sh2_fb_write_w,
			.read_8 = s32x_sh2_fb_read_b, .write_8 = s32x_sh2_fb_write_b},
		{0x4020000, 0x4040000, .mask = 0x7FFFFFF, .read_16 = s32x_sh2_fb_read_w, .write_16 = s32x_sh2_overwrite_write_w,
			.read_8 = s32x_sh2_fb_read_b, .write_8 = s32x_sh2_overwrite_write_b},
		{0x2000000, 0x2400000, .mask = 0x3FFFFF, .flags = MMAP_READ | MMAP_PTR_IDX | MMAP_AUX_BUFF, .ptr_index = 0,
			.read_cycles = 6, .write_cycles = 3, .burst_cycles = 6 * 8},
		{0x0004000, 0x0004400, .mask = 0x7FFFFFF, .read_16 = s32x_sh2_read, .write_16 = s32x_sh2_write,
			.read_8 = s32x_sh2_read_b, .write_8 = s32x_sh2_write_b},
		{0x0000000, 0x0004000, .mask = 0x7FFFFFF, .flags = MMAP_READ,
			.read_cycles = 3, .write_cycles = 3, .burst_cycles = 3 * 8},
	};
	static const size_t num_chunks = sizeof(base_sh2_map)/sizeof(*base_sh2_map);
	s32x *ret = calloc(1, sizeof(s32x));
	ret->sdram = aligned_calloc(128*1024, sizeof(uint16_t), 16);

	memmap_chunk *main_map = calloc(num_chunks, sizeof(memmap_chunk));
	memcpy(main_map, base_sh2_map, sizeof(base_sh2_map));
	main_map[0].buffer = ret->sdram;
	if (cd_boot) {
		//TODO: BRAM cart support?
		main_map[3].flags &= ~MMAP_AUX_BUFF;
	} else {
		main_map[3].buffer = media->buffer;
		main_map[3].mask &= nearest_pow2(media->size) - 1;
	}
	if (arb_enabled()) {
		main_map[3].flags |= MMAP_FUNC_NULL;
		main_map[3].read_16 = arb_sh2_rom_read_w;
		main_map[3].read_8 = arb_sh2_rom_read_b;
		arb_cart_mask = main_map[3].mask;
	}
	main_map[5].buffer = aligned_calloc(1, main_map[5].end, 16);
	char *main_path = tern_find_path_default(config, "system\0s32x_main_bios\0", (tern_val){.ptrval = "32X_M_BIOS.bin"}, TVAL_PTR).ptrval;
	FILE *f = fopen(main_path, "rb");
	if (f) {
		fread(main_map[5].buffer, 1, main_map[5].end, f);
		byteswap_rom(main_map[5].end, main_map[5].buffer);
		fclose(f);
	} else {
		warning("32X Main SH2 BIOS not found at %s. 32X will not function correctly until you fix your config\n", main_path);
	}
	sh2_options *main_opts = calloc(1, sizeof(sh2_options));
	init_sh2_opts(main_opts, main_map, num_chunks);
	ret->main = init_sh2_context(main_opts, main_sh2_next_int);
	sh7095_setup(ret->main);
	ret->main->sync_cycle = 0xFFFFFFFF;
	ret->main->system = ret;
	ret->main->main = 1;
	ret->main_tmp = calloc(1, sizeof(sh2_context));
	ret->main->write32[0] = ret->main->write32[1] = s32x_sh2_write_external_32;
	ret->main->read32[0] = ret->main->read32[1] = s32x_sh2_read_external_32;

	memmap_chunk *sub_map = calloc(num_chunks, sizeof(memmap_chunk));
	memcpy(sub_map, base_sh2_map, sizeof(base_sh2_map));
	sub_map[0].buffer = ret->sdram;
	if (arb_enabled()) {
		sub_map[3].flags |= MMAP_FUNC_NULL;
		sub_map[3].read_16 = arb_sh2_rom_read_w;
		sub_map[3].read_8 = arb_sh2_rom_read_b;
	}
	if (cd_boot) {
		//TODO: BRAM cart support?
		sub_map[3].flags &= ~MMAP_AUX_BUFF;
	} else {
		sub_map[3].buffer = media->buffer;
		sub_map[3].mask &= nearest_pow2(media->size) - 1;
	
	}
	sub_map[5].buffer = aligned_calloc(1, sub_map[5].end, 16);
	char *sub_path = tern_find_path_default(config, "system\0s32x_sub_bios\0", (tern_val){.ptrval = "32X_S_BIOS.bin"}, TVAL_PTR).ptrval;
	f = fopen(sub_path, "rb");
	if (f) {
		fread(sub_map[5].buffer, 1, sub_map[5].end, f);
		byteswap_rom(sub_map[5].end, sub_map[5].buffer);
		fclose(f);
	} else {
		warning("32X Sub SH2 BIOS not found at %s. 32X will not function correctly until you fix your config\n", sub_path);
	}
	sh2_options *sub_opts = calloc(1, sizeof(sh2_options));
	init_sh2_opts(sub_opts, sub_map, num_chunks);
	ret->sub = init_sh2_context(sub_opts, sub_sh2_next_int);
	sh7095_setup(ret->sub);
	ret->sub->sync_cycle = 0xFFFFFFFF;
	ret->sub->system = ret;
	ret->sub_tmp = calloc(1, sizeof(sh2_context));
	ret->sub->write32[0] = ret->sub->write32[1] = s32x_sh2_write_external_32;
	ret->sub->read32[0] = ret->sub->read32[1] = s32x_sh2_read_external_32;
	
	//hook up main/sub SCI
	sh7095_periph *p = ret->main->periph_state;
	p->sci_handler_data = ret->sub;
	p->transmit_handler = sh7095_sci_to_sh7095_sci;
	p = ret->sub->periph_state;
	p->sci_handler_data = ret->main;
	p->transmit_handler = sh7095_sci_to_sh7095_sci;

	sh2_assert_reset(ret->main);
	sh2_assert_reset(ret->sub);
	sh2_clear_reset(ret->main);
	sh2_clear_reset(ret->sub);
	s32x_video_init(&ret->video, pal);
	ret->rom = media->buffer;
	ret->regs[S32X_ADAPT_CTRL] = 0x0082;
	ret->regs[S32X_PWM_WIDTH_L] = BIT_PWM_EMPTY;
	ret->regs[S32X_PWM_WIDTH_R] = BIT_PWM_EMPTY;
	ret->vector_rom = get_68K_vector_rom(media->size);
	if (cd_boot) {
		ret->sh2_regs[S32X_SH2_INT_CTRL] |= BIT_CART_SH2;
	}
	ret->pwm = render_audio_source("PWM", (pal ? MCLKS_PAL : MCLKS_NTSC) * 3, 7 * PWM_DECIMATE, 2);
	return ret;
}

void free_32x(s32x *mars)
{
	render_free_source(mars->pwm);
	free(mars->vector_rom);
	s32x_video_free(&mars->video);
	sh7095_free(mars->sub);
	sh7095_free(mars->main);
	aligned_free(mars->main->opts->gen.memmap[5].buffer);
	aligned_free(mars->sub->opts->gen.memmap[5].buffer);
	free(mars->main->opts);
	free(mars->sub->opts);
	sh2_free(mars->main);
	sh2_free(mars->sub);
	aligned_free(mars->sdram);
	free(mars);
}

