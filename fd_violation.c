/* CS631 start */

#include "postgres.h"

#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <unistd.h>
#include <sys/socket.h>
#ifdef HAVE_SYS_SELECT_H
#include <sys/select.h>
#endif
#ifdef HAVE_SYS_RESOURCE_H
#include <sys/time.h>
#include <sys/resource.h>
#endif

#ifndef HAVE_GETRUSAGE
#include "rusagestub.h"
#endif

#include "executor/spi.h"

#include "access/parallel.h"
#include "access/printtup.h"
#include "access/xact.h"
#include "catalog/pg_type.h"
#include "commands/async.h"
#include "commands/prepare.h"
#include "jit/jit.h"
#include "libpq/libpq.h"
#include "libpq/pqformat.h"
#include "libpq/pqsignal.h"
#include "mb/pg_wchar.h"
#include "mb/stringinfo_mb.h"
#include "miscadmin.h"
#include "nodes/print.h"
#include "optimizer/optimizer.h"
#include "parser/analyze.h"
#include "parser/parser.h"
#include "pg_getopt.h"
#include "pg_trace.h"
#include "pgstat.h"
#include "postmaster/autovacuum.h"
#include "postmaster/interrupt.h"
#include "postmaster/postmaster.h"
#include "replication/logicallauncher.h"
#include "replication/logicalworker.h"
#include "replication/slot.h"
#include "replication/walsender.h"
#include "rewrite/rewriteHandler.h"
#include "storage/bufmgr.h"
#include "storage/ipc.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/procsignal.h"
#include "storage/sinval.h"
#include "tcop/fastpath.h"
#include "tcop/pquery.h"
#include "tcop/tcopprot.h"
#include "tcop/utility.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/ps_status.h"
#include "utils/snapmgr.h"
#include "utils/timeout.h"
#include "utils/timestamp.h"

static int errdetail_abort(void);


void get_column_names_and_values_1(const char *query_str,int query_len,char col_names[][100], char col_values[][100], int it,int *no_of_cols);
void get_column_names_and_values_2(const char *query_str,int quert_len,char table_name[],char col_names[][100], char col_values[][100], int it,int *no_of_cols);
void handle_fd_table_insertion(int no_of_cols,char col_names[][100],char col_values[][100]);
void handle_other_tables_insertion(char table_name[],int no_of_cols,char col_names[][100],char col_values[][100]);
void space_traverse(const char *query_str, int query_len,int *it){
	while(*it < query_len && query_str[*it] == ' ')
	{
		*it = *it + 1;
	}
}
void nonspace_traverse(const char *query_str, int query_len,int *it){
	while(*it < query_len && query_str[*it] != ' ')
	{
		*it = *it + 1;
	}
}

void check_update_fd_violation(const char *query_str,int query_len,int it){
	space_traverse(query_str,query_len,&it);
	char tablename[100];
	int j=0;
	while(it < query_len && query_str[it] != ' ')
	{
		tablename[j++] = query_str[it++];
	}
	tablename[j]='\0';
	space_traverse(query_str,query_len,&it);
	nonspace_traverse(query_str,query_len,&it);
	space_traverse(query_str,query_len,&it);
	char update_col[100];
	j=0;
	while(it < query_len && query_str[it] != '=')
	{
		update_col[j++] = query_str[it++];
	}
	update_col[j] = '\0';
	++it;
	char update_val[100];
	j=0;
	while(it < query_len && query_str[it] != ' ')
	{
		update_val[j++] = query_str[it++];
	}
	update_val[j] = '\0';
	space_traverse(query_str,query_len,&it);
	nonspace_traverse(query_str,query_len,&it);
	space_traverse(query_str,query_len,&it);
	char condition_col[100];
	j=0;
	while(it < query_len && query_str[it] != '=')
	{
		condition_col[j++] = query_str[it++];
	}
	condition_col[j] = '\0';
	++it;
	char condition_val[100];
	j=0;
	while(it < query_len && query_str[it] != ';')
	{
		condition_val[j++] = query_str[it++];
	}
	condition_val[j] = '\0';

	char query_fdcols[512];
	sprintf(query_fdcols,"SELECT det_col,dep_col FROM fd_table WHERE relation_name='%s';",tablename);
	int con_ret = SPI_connect();
	if(con_ret == SPI_OK_CONNECT)
	{
		int exec_ret = SPI_exec(query_fdcols,0);
		if(exec_ret > 0 && SPI_tuptable != NULL)
		{
			SPITupleTable *crawl = SPI_tuptable;
			TupleDesc crawl_desc = crawl->tupdesc;

			for (int j = 0; j < crawl->numvals; j++)
			{
				HeapTuple temp = crawl->vals[j];
				char det_col[256],dep_col[256];
				bzero(det_col,256);
				bzero(dep_col,256);
				sprintf(det_col,SPI_getvalue(temp, crawl_desc, 1));
				sprintf(dep_col,SPI_getvalue(temp, crawl_desc, 2));

				if(strcmp(det_col,update_col) == 0 && strcmp(dep_col,condition_col)==0)
				{
					char query_fdval[512];
					bzero(query_fdval,512);
					if(update_col[0] == '\'')
					{
						sprintf(query_fdval,"SELECT %s FROM %s WHERE %s LIKE %s",dep_col,tablename,det_col,update_val);
					}
					else
					{
						sprintf(query_fdval,"SELECT %s FROM %s WHERE %s=%s",dep_col,tablename,det_col,update_val);
					}

					exec_ret = SPI_exec(query_fdval,0);
					if(exec_ret > 1 && SPI_tuptable != NULL)
					{
						SPITupleTable *crawl_= SPI_tuptable;
						TupleDesc crawl_desc_ = crawl_->tupdesc;

						for(int t=0;t< crawl_->numvals; ++t)
						{
							HeapTuple temp_ = crawl_->vals[t];
							char dep_val[256];
							bzero(dep_val,256);
							sprintf(dep_val,SPI_getvalue(temp_,crawl_desc_,1));
							char col_dep_val[100];
							int len_dep = strlen(condition_val);
							if(condition_val[0]=='\'')
							{
								int i;
								for(i=1;i<len_dep-1;++i)
								{
									col_dep_val[i-1]=condition_val[i];
								}
								col_dep_val[i]='\0';
							}
							else
							{
								strcpy(col_dep_val,condition_val);
							}

							if(strcmp(dep_val,col_dep_val) != 0)
							{
								ereport(ERROR,(errcode(ERRCODE_FUNCTIONAL_DEPENDENCY_VIOLATION),errmsg("Updation Aborted, ""Functional Dependency Violation: this value '%s' in '%s' has multiple values in '%s'", update_val, det_col, dep_col)));
							}
						}
					}

				}


			}
		}
	}
	SPI_finish();



}
void check_insert_fd_violation(const char *query_str,int query_len,int it){

    /* 1.1 Extract the table name from the query */

	space_traverse(query_str,query_len,&it);
	nonspace_traverse(query_str,query_len,&it);
	space_traverse(query_str,query_len,&it);

    char table_name[100];
    int j=0;
    while(it < query_len && query_str[it] != ' ' && query_str[it] != '(')
    {
        table_name[j++] = query_str[it++];
    }
    space_traverse(query_str,query_len,&it);
    table_name[j] = '\0';

    /* Extraction of column names and column values*/
    char col_names[256][100],col_values[256][100];
	int no_of_cols = 0;


    /*
    * 1.2 Here we are considering insertion queries of two types
    *     (a) INSERT INTO TABLE_NAME(col1,col2,col3....) VALUES(val1,val2,val3....)
    *     (b) INSERT INTO TABLE_NAME VALUES(val1,val2,val3.......)
    */


    /* Extracting column names and column values from (a) INSERT INTO TABLE_NAME(col1,col2,col3....) VALUES(val1,val2,val3....) case of Insertion */
    if(query_str[it] == '(')
    {
        get_column_names_and_values_1(query_str,query_len,col_names,col_values,it,&no_of_cols);
    }
    /* Extracting column names and values from 1.2 (b) INSERT INTO TABLE_NAME VALUES(val1,val2,val3.......) case of Insertion */
    else
    {
        get_column_names_and_values_2(query_str,query_len,table_name,col_names,col_values,it,&no_of_cols);
    }
    

    /*
    * If insertion is in fd_table we insert the values and then create an index on Table on the determinent column ( A-> B) [ determinent column here is A ]
    * This is useful for faster retrieval of Data.
    */
    int ans = 0;
    if(strcmp(table_name,"fd_table")  == 0)
    {
        handle_fd_table_insertion(no_of_cols,col_names,col_values);
    }
    else
    {
        handle_other_tables_insertion(table_name,no_of_cols,col_names,col_values);
    }

}

void get_column_names_and_values_1(const char *query_str,int query_len,char col_names[][100],char col_values[][100],int it,int *no_of_cols)
{
    /*
    * Extracting all column names of the table from the query
    */
    char col_str[1024];
    ++it;
    int j=0;
    while(it < query_len && query_str[it] != ')')
    {
        col_str[j++] = query_str[it++];
    }
    col_str[j] = '\0';
    int c = 0;
    char *tk = strtok(col_str,",");

    while(tk != NULL)
    {
        strcpy(col_names[c],tk);
        tk = strtok(NULL, ",");
        ++c;
    }
    *no_of_cols = c;

    /*
    * Extracting all the values from the query
    */
    while(it < query_len && query_str[it] != '(' )
    {
        ++it;
    }
    ++it;
    char val_str[1024];
    j=0;
    while(it < query_len && query_str[it] != ')')
    {
        val_str[j++] = query_str[it++];
    }
    val_str[j] = '\0';
    c = 0;
    tk = strtok(val_str,",");
    while( tk != NULL)
    {
        strcpy(col_values[c],tk);
        tk = strtok(NULL,",");
        ++c;
    }
}


void get_column_names_and_values_2(const char *query_str,int query_len,char table_name[],char col_names[][100],char col_values[][100],int it,int *no_of_cols)
{
    /*
        * Extracting all column values in the insert statement
        */
    char val_str[1024];
    while(it < query_len && query_str[it] != '(')
    {
        ++it;
    }
    ++it;
    int j=0;
    while(it < query_len && query_str[it] != ')')
    {
        val_str[j++] = query_str[it++];
    }
    val_str[j] = '\0';
    char *tk = strtok(val_str,",");
    int c =0;
    while( tk != NULL)
    {
        strcpy(col_values[c],tk);
        tk = strtok(NULL,",");
        ++c;
    }

    /*
    * Connecting to database and retrieving the column names of the table in which insertions are done
    */
    int con_ret = SPI_connect();
    int cols = 0;
    if(con_ret == SPI_OK_CONNECT)
    {
        char query_col[512];
        bzero(query_col,512);
        sprintf(query_col, "SELECT column_name FROM information_schema.columns WHERE table_name='%s';",table_name);
        int exec_ret,proc_ret;
        exec_ret = SPI_exec(query_col,0);
        if(exec_ret > 0 && SPI_tuptable != NULL)
        {
            SPITupleTable *crawl = SPI_tuptable;
            TupleDesc crawl_desc = crawl->tupdesc;
            for (j = 0; j < crawl->numvals; j++)
            {
                HeapTuple temp = crawl->vals[j];

                sprintf(col_names[cols],SPI_getvalue(temp, crawl_desc, 1));
                ++cols;
            }

        }
    }
    *no_of_cols = cols;
    SPI_finish();

}

void handle_fd_table_insertion(int no_of_cols,char col_names[][100],char col_values[][100])
{
    int det_ind, table_ind;
    for(int t=0;t<no_of_cols;++t)
    {
        if(strcmp(col_names[t],"det_col") == 0)
        {
            det_ind = t;
        }
        else if(strcmp(col_names[t],"relation_name") == 0)
        {
            table_ind = t;
        }
    }
    char query_index[512];
    bzero(query_index,512);
    char r_name[32],d_name[32];
    int t;
    for(t=1;t<strlen(col_values[table_ind])-1;++t)
    {
        r_name[t-1] = col_values[table_ind][t];
    }
    r_name[t-1]='\0';
    for(t=1;t<strlen(col_values[det_ind])-1;++t)
    {
        d_name[t-1] = col_values[det_ind][t];
    }
    d_name[t-1] = '\0';
    sprintf(query_index,"CREATE INDEX index_%s_%s ON %s (%s);",r_name,d_name,r_name,d_name);
    int con_ret_ind = SPI_connect();
    if(con_ret_ind == SPI_OK_CONNECT)
    {
        int exec_ret_ind = SPI_exec(query_index,0);
    }
    SPI_finish();

}

void handle_other_tables_insertion(char table_name[],int no_of_cols,char col_names[][100],char col_values[][100])
{
    /*
    * Checking for any Functional dependency violations  during insertion
    */
    int res = 1;
    char query_fdcols[512];
    bzero(query_fdcols,512);
    sprintf(query_fdcols,"SELECT det_col,dep_col FROM fd_table WHERE relation_name='%s';",table_name);
    //printf("%s\n",query_fdcols);
    int con_ret = SPI_connect();
    if(con_ret == SPI_OK_CONNECT)
    {
        int exec_ret = SPI_exec(query_fdcols,0);
        if(exec_ret > 0 && SPI_tuptable != NULL)
        {
            SPITupleTable *crawl = SPI_tuptable;
            TupleDesc crawl_desc = crawl->tupdesc;
            //printf("No of fds = %d\n",crawl->numvals);
            for (int j = 0; j < crawl->numvals; j++)
            {
                HeapTuple temp = crawl->vals[j];
                char det_col[256],dep_col[256];
                bzero(det_col,256);
                bzero(dep_col,256);
                sprintf(det_col,SPI_getvalue(temp, crawl_desc, 1));
                sprintf(dep_col,SPI_getvalue(temp, crawl_desc, 2));
                //printf("%s %s \n",det_col,dep_col);
                int det_ind ,dep_ind;
                for(int t = 0;t<no_of_cols;++t)
                {
                    if(strcmp(col_names[t],det_col) == 0)
                    {
                        det_ind = t;
                        break;
                    }
                }
                for(int t=0;t< no_of_cols ;++t)
                {
                    if(strcmp(col_names[t],dep_col) == 0)
                    {
                        dep_ind = t;
                        break;
                    }
                }
                char query_fdval[512];
                bzero(query_fdval,512);
                if(col_values[det_ind][0] == '\'')
                {
                	sprintf(query_fdval,"SELECT %s FROM %s WHERE %s LIKE %s",dep_col,table_name,det_col,col_values[det_ind]);
                }
                else
                {
                	sprintf(query_fdval,"SELECT %s FROM %s WHERE %s=%s",dep_col,table_name,det_col,col_values[det_ind]);
                }

                //printf("%s\n",query_fdval);
                exec_ret = SPI_exec(query_fdval,0);
                if(exec_ret > 1 && SPI_tuptable != NULL)
                {
                    SPITupleTable *crawl_= SPI_tuptable;
                    TupleDesc crawl_desc_ = crawl_->tupdesc;
                    //printf("%d\n",crawl->numvals);
                    for(int t=0;t< crawl_->numvals; ++t)
                    {
                        HeapTuple temp_ = crawl_->vals[t];
                        char dep_val[256];
                        bzero(dep_val,256);
                        sprintf(dep_val,SPI_getvalue(temp_,crawl_desc_,1));
                        /*
						* Check if for the A->B dependency the value of B that is to inserted is same as the one that is already present
						*/
                        char col_dep_val[100];
                        int len_dep = strlen(col_values[dep_ind]);
                        if(col_values[dep_ind][0]=='\'')
						{
                        	int i;
							for(i=1;i<len_dep-1;++i)
							{
								col_dep_val[i-1]=col_values[dep_ind][i];
							}
							col_dep_val[i]='\0';
						}
                        else
                        {
                        	strcpy(col_dep_val,col_values[dep_ind]);
                        }

                        //printf("%s %s\n",dep_val,col_val_dep);
                        // char left_side[10];
                        // for(int t=0;col_values[dep_ind]!=NULL;t++){

                        // }
                        if(strcmp(dep_val,col_dep_val) != 0)
                        {
                            ereport(ERROR,(errcode(ERRCODE_FUNCTIONAL_DEPENDENCY_VIOLATION),errmsg("Insertion Aborted, ""Functional Dependency Violation: this value '%s' in '%s' has multiple values in '%s'", col_values[det_ind], det_col, dep_col)));
                        }
                    }
                }
            }
        }
    }
    SPI_finish();
}
/* CS631 end */
